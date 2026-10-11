#!/usr/bin/env python3
"""Format explicit Goose files, or tracked files changed since a Git revision.

Only whitespace between tokens changes. Braces expand, statements split after
semicolons, declarations receive blank lines, and common operators receive
spaces. Existing line breaks remain; ambiguous angle and reference punctuation
retains its original spacing.
"""

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys


class FormatError(ValueError):
    """Source cannot be safely formatted."""


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    gap: str


OPERATORS = tuple(sorted((
    '(', ')', '[', ']', '{', '}', ',', ';', ':', '?', '::', '.', '..', '.=',
    '.==', '.!=', '+', '-', '*', '/', '%', '+=', '-=', '*=', '/=', '%=', '&=',
    '|=', '^=', '++', '--', '=', '==', '!=', '<', '>', '<=', '>=', '<<', '>>',
    '<<=', '>>=', '!', '~', '&', '|', '^', '&&', '||', '->', '=>',
), key=len, reverse=True))
NUMBER = re.compile(r'(?:0[xX][0-9a-fA-F]+(?:\.[0-9a-fA-F]+)?(?:[pP][+-]?[0-9]+)?|'
                    r'[0-9]+(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)')
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z_0-9]*')
HEX_DIGITS = frozenset('0123456789abcdefABCDEF')


def tokenize(source: str) -> list[Token]:
    """Keep literal and comment spelling, including raw-string indentation."""
    tokens = []
    position = 1 if source.startswith('\ufeff') else 0

    def fail(message: str, offset: int) -> None:
        line = source.count('\n', 0, offset) + 1
        raise FormatError(f'line {line}: {message}')

    def escaped_character(offset: int, start: int) -> int:
        if offset >= len(source) or source[offset] in '\n\x00':
            fail('unterminated quoted literal', start)
        if source[offset] != '\\':
            return offset + 1
        if offset + 1 >= len(source):
            fail('unterminated escape', start)
        escape = source[offset + 1]
        if escape == 'x':
            digits = source[offset + 2:offset + 4]
            if len(digits) != 2 or any(c not in HEX_DIGITS for c in digits):
                fail('hex escape requires two digits', offset)
            return offset + 4
        if escape not in 'ntr0\\"\'':
            fail('unknown escape sequence', offset)
        return offset + 2

    while position < len(source):
        gap_start = position
        while position < len(source) and source[position] in ' \t\r\n':
            position += 1
        gap = source[gap_start:position]
        if position == len(source):
            break
        start = position
        if source.startswith('//', position):
            end = source.find('\n', position)
            position = len(source) if end < 0 else end
            kind = 'line_comment'
        elif source.startswith('/*', position):
            position += 2
            nesting = 1
            while nesting and position < len(source):
                if source.startswith('/*', position):
                    nesting += 1
                    position += 2
                elif source.startswith('*/', position):
                    nesting -= 1
                    position += 2
                else:
                    position += 1
            if nesting:
                fail('unterminated block comment', start)
            kind = 'block_comment'
        elif source.startswith('"""', position):
            end = source.find('"""', position + 3)
            if end < 0:
                fail('unterminated raw string', start)
            body = source[position + 3:end]
            if '\n' in body:
                opening, rest = body.split('\n', 1)
                if opening.strip(' \t\r'):
                    fail('raw string opening must end its line', start)
                margin = rest.rsplit('\n', 1)[-1]
                if margin.strip(' \t'):
                    fail('raw string closing must follow only indentation', end)
                for line in rest.split('\n')[:-1]:
                    line = line.removesuffix('\r')
                    if line.strip(' \t') and not line.startswith(margin):
                        fail('raw string line does not match closing indentation', start)
            position = end + 3
            kind = 'literal'
        elif source[position] in '\'"':
            quote = source[position]
            position += 1
            if quote == "'":
                position = escaped_character(position, start)
                if position >= len(source) or source[position] != quote:
                    fail('character literal must contain one character', start)
            else:
                while position < len(source) and source[position] != quote:
                    position = escaped_character(position, start)
                if position == len(source):
                    fail('unterminated string literal', start)
            position += 1
            kind = 'literal'
        elif '0' <= source[position] <= '9':
            match = NUMBER.match(source, position)
            position = match.end()
            text = match.group()
            if text.lower().startswith('0x'):
                if '.' in text and 'p' not in text.lower():
                    fail('hex float requires a p exponent', start)
                if position < len(source) and source[position] in 'pP':
                    fail('hex float exponent requires digits', start)
                if '.' not in text and 'p' not in text.lower() and int(text, 16) > 2**64 - 1:
                    fail('integer literal exceeds 64 bits', start)
            elif source[start:start + 2].lower() == '0x':
                fail('hex digits expected after 0x', start)
            elif not any(c in text for c in '.eE') and int(text) > 2**64 - 1:
                fail('integer literal exceeds 64 bits', start)
            kind = 'number'
        elif match := IDENTIFIER.match(source, position):
            position = match.end()
            kind = 'word'
        else:
            operator = next((op for op in OPERATORS if source.startswith(op, position)), None)
            if operator is None:
                fail(f'illegal character {source[position]!r}', position)
            position += len(operator)
            kind = 'punctuation'
        text = source[start:position]
        if '\x00' in text:
            fail('embedded null character', start)
        tokens.append(Token(kind, text, gap))
    return tokens


@dataclass
class Delimiter:
    text: str
    is_match: bool = False
    arm_body: bool = False


SPACED = frozenset(('=', '==', '!=', '+', '-', '*', '/', '%', '+=', '-=', '*=',
                    '/=', '%=', '&=', '|=', '^=', '<=', '>=', '<<=', '>>=',
                    '|', '^', '&&', '||', '->', '=>', '.=', '.==', '.!=', '<<'))
PREFIX_CONTEXT = SPACED | frozenset(('(', '[', '{', ',', ';', ':', 'return',
                                   'break', 'in', 'if', 'while', 'guard', '..'))
CONSERVATIVE = frozenset(('<', '>', '>>', '&', '?'))


def declaration_separators(tokens: list[Token]) -> set[int]:
    """Keep import and global-binding runs together, with space around declarations.

    A standalone comment after a completed declaration belongs to the next
    declaration, so its separator precedes the comment rather than its name.
    """
    separators = set()
    depth = 0
    start = None
    leading_comment = None
    group = None
    previous_group = None
    for index, token in enumerate(tokens):
        if token.kind.endswith('comment'):
            if start is None and leading_comment is None and ('\n' in token.gap or index == 0):
                leading_comment = index
            continue
        if start is None:
            start = leading_comment if leading_comment is not None else index
            leading_comment = None
            group = ('imports' if token.text == 'import' else
                     'bindings' if token.text in ('let', 'var', 'const', 'reusable') else
                     'declaration')
            if previous_group is not None and (group != previous_group or group == 'declaration'):
                separators.add(start)
        if token.text in ('(', '[', '{'):
            depth += 1
        elif token.text in (')', ']', '}'):
            depth -= 1
        if depth == 0 and (token.text == ';' or token.text == '}' and group == 'declaration'):
            previous_group = group
            start = None
    return separators


def scalar_binary_operator(tokens: list[Token], index: int) -> bool:
    """Literals distinguish comparisons and bit operations from type suffixes.

    Named operands alone can also be generic arguments or reference qualifiers;
    retain their spacing rather than guessing which grammar the parser selects.
    """
    if tokens[index].text not in ('<', '>', '>>', '&') or index == 0 or index + 1 == len(tokens):
        return False
    before, after = tokens[index - 1], tokens[index + 1]
    ends_operand = before.kind in ('word', 'number', 'literal') or before.text in (')', ']')
    starts_operand = after.kind in ('word', 'number', 'literal') or after.text in ('(', '-', '!', '~')
    return ends_operand and starts_operand and (
        before.kind in ('number', 'literal') or after.kind in ('number', 'literal')
    )


def format_source(source: str) -> str:
    """Change layout without changing the compiler's token sequence."""
    tokens = tokenize(source)
    if not tokens:
        return '\ufeff' if source.startswith('\ufeff') else ''
    parts = ['\ufeff'] if source.startswith('\ufeff') else []
    at_start = True
    delimiters: list[Delimiter] = []
    previous = None
    previous_prefix = False
    pending_break = False
    header = []
    separators = declaration_separators(tokens)
    previous_binary = False

    def newline(blank: bool = False) -> None:
        nonlocal at_start
        if not at_start:
            parts.append('\n')
            at_start = True
        if blank and parts and parts[-1] != '\n\n':
            # A single blank line keeps groups without retaining empty runs.
            if len(parts) >= 2 and parts[-1] == '\n' and parts[-2] == '\n':
                return
            parts.append('\n')

    def emit(text: str, space: bool = False) -> None:
        nonlocal at_start
        if at_start:
            parts.append('    ' * len(delimiters))
        elif space:
            parts.append(' ')
        parts.append(text)
        at_start = text.endswith('\n')

    for index, token in enumerate(tokens):
        text = token.text
        original_break = '\n' in token.gap
        comment = token.kind.endswith('comment')
        if index in separators:
            newline(blank=True)
        if comment:
            if original_break:
                newline(token.gap.count('\n') > 1)
                pending_break = False
            emit(text, space=not at_start)
            if token.kind == 'line_comment' or '\n' in text:
                newline()
                pending_break = False
            previous = token
            previous_prefix = False
            previous_binary = False
            continue

        closes = text in (')', ']', '}')
        if closes:
            expected = {')': '(', ']': '[', '}': '{'}[text]
            if not delimiters or delimiters[-1].text != expected:
                raise FormatError(f'unmatched {text!r}')
            delimiters.pop()
        attached = (text in (';', ',', ')', ']', '.', '::', 'else') or text in SPACED
                    or text == '}' and previous and previous.text == '{')
        if pending_break and not (previous and previous.text in ('{', '}') and attached):
            newline()
        pending_break = False
        if text == '}':
            if previous and previous.text != '{':
                newline()
        elif original_break:
            newline(token.gap.count('\n') > 1)

        before = previous.text if previous else ''
        cast_marker = text == '!' and before == 'as'
        prefix = text in ('!', '~') and not cast_marker or text in ('-', '&') and (
            previous is None or previous_prefix or previous_binary or previous.text in PREFIX_CONTEXT
        )
        binary = text in SPACED and not prefix or scalar_binary_operator(tokens, index)
        space = False
        if previous:
            if previous.kind.endswith('comment'):
                space = text not in (',', ';', ')', ']', '.', '::')
            elif text == '{':
                space = True
            elif text in (',', ';', ')', ']', '.', '::', ':') or text == '}' and before == '{':
                space = False
            elif cast_marker:
                space = False
            elif before in ('.', '::', '(', '['):
                space = False
            elif previous_prefix:
                space = False
            elif binary or previous_binary or before in (',', ':', ';', '}'):
                space = True
            elif prefix:
                space = before not in ('!', '~')
            elif text in CONSERVATIVE or before in CONSERVATIVE:
                space = bool(token.gap)
            elif text == '(':
                space = before in ('if', 'while', 'match', 'for', 'guard')
            elif text == '[' or text in ('++', '--', '..') or before == '..':
                space = False
            elif text in ('!', '~'):
                space = bool(token.gap)
            else:
                space = True
        # Separate adjacent punctuation whenever joining it would form another
        # operator or start a comment, including unary minus after subtraction.
        if previous and not space and not at_start:
            joined = previous.text + text
            if (previous.kind == token.kind == 'punctuation'
                    and (joined in OPERATORS or joined.startswith(('//', '/*')))):
                space = True
        emit(text, space)

        if text in ('(', '[', '{'):
            delimiters.append(Delimiter(text, is_match=text == '{' and 'match' in header))
            if text == '{':
                header = []
                pending_break = True
        elif text == '}':
            header = []
            pending_break = True
        elif text == ';':
            if not delimiters or delimiters[-1].text == '{':
                pending_break = True
            header = []
        elif text == '=>' and delimiters and delimiters[-1].is_match:
            delimiters[-1].arm_body = True
        elif text == ',' and delimiters and delimiters[-1].text == '{':
            frame = delimiters[-1]
            if not frame.is_match or frame.arm_body:
                pending_break = True
                frame.arm_body = False
                header = []
        else:
            header.append(text)
        previous = token
        previous_prefix = prefix
        previous_binary = binary

    if delimiters:
        raise FormatError(f'unclosed {delimiters[-1].text!r}')
    newline()
    result = ''.join(parts)
    if [(t.kind, t.text) for t in tokenize(result)] != [(t.kind, t.text) for t in tokens]:
        raise FormatError('formatting would change the token sequence')
    return result


def changed_files(revision: str) -> list[Path]:
    result = subprocess.run(
        ['git', 'diff', '--name-only', '-z', '--diff-filter=ACMR', revision,
         '--', '*.goose'], capture_output=True,
    )
    if result.returncode:
        raise FormatError(result.stderr.decode('utf-8', errors='replace').strip())
    root_result = subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                                 capture_output=True)
    if root_result.returncode:
        raise FormatError(root_result.stderr.decode('utf-8', errors='replace').strip())
    root = Path(root_result.stdout.decode('utf-8').strip())
    return [root / name.decode('utf-8') for name in result.stdout.split(b'\0')
            if name and not name.startswith(b'test/errors/')]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='report files needing formatting')
    parser.add_argument('--changed-since', metavar='REF', help='select tracked changes from REF')
    parser.add_argument('files', nargs='*', type=Path)
    args = parser.parse_args(argv)
    if not args.files and args.changed_since is None:
        parser.error('supply files or --changed-since REF')
    try:
        paths = args.files + (changed_files(args.changed_since) if args.changed_since else [])
        changes = []
        for path in dict.fromkeys(paths):
            with path.open(encoding='utf-8', newline='') as stream:
                source = stream.read()
            try:
                formatted = format_source(source)
            except FormatError as error:
                raise FormatError(f'{path}: {error}') from error
            if formatted != source:
                changes.append((path, formatted))
        for path, formatted in changes:
            if args.check:
                print(f'needs formatting: {path}')
            else:
                with path.open('w', encoding='utf-8', newline='') as stream:
                    stream.write(formatted)
                print(f'formatted: {path}')
        return 1 if args.check and changes else 0
    except (FormatError, OSError, UnicodeError) as error:
        print(f'format_goose: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
