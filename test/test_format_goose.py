"""Behavior checks for the standalone Goose formatter."""

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "format_goose.py"
spec = importlib.util.spec_from_file_location("format_goose", SCRIPT)
formatter = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = formatter
spec.loader.exec_module(formatter)


class FormatTests(unittest.TestCase):
    def assert_preserved(self, source):
        result = formatter.format_source(source)
        self.assertEqual(
            [(token.kind, token.text) for token in formatter.tokenize(source)],
            [(token.kind, token.text) for token in formatter.tokenize(result)],
        )
        self.assertEqual(formatter.format_source(result), result)
        return result

    def test_reordered_reference_fields(self):
        source = (
            "struct Owner {first:i64[>..]&,second:i64[>..]&}\n"
            "fn main() {\n"
            "var a:i64[>..]=[];var b:i64[>..]=[];\n"
            "match hold {Arrays h=>{h.first.push(11);h.second.push(13);}};\n"
            "assert(a.len==1&&b.len==1);\n"
            "}\n"
        )
        self.assertEqual(self.assert_preserved(source), (
            "struct Owner {\n"
            "    first: i64[>..]&,\n"
            "    second: i64[>..]&\n"
            "}\n"
            "\n"
            "fn main() {\n"
            "    var a: i64[>..] = [];\n"
            "    var b: i64[>..] = [];\n"
            "    match hold {\n"
            "        Arrays h => {\n"
            "            h.first.push(11);\n"
            "            h.second.push(13);\n"
            "        }\n"
            "    };\n"
            "    assert(a.len == 1 && b.len == 1);\n"
            "}\n"
        ))

    def test_adjacent_struct_and_enum_declarations(self):
        source = (
            'struct Owner {first:i64[>..]&,second:i64[>..]&}\n'
            'enum Hold {Arrays {first:i64[>..]&,second:i64[>..]&}}'
        )
        self.assertEqual(self.assert_preserved(source), (
            'struct Owner {\n'
            '    first: i64[>..]&,\n'
            '    second: i64[>..]&\n'
            '}\n'
            '\n'
            'enum Hold {\n'
            '    Arrays {\n'
            '        first: i64[>..]&,\n'
            '        second: i64[>..]&\n'
            '    }\n'
            '}\n'
        ))

    def test_top_level_groups_and_declaration_comments(self):
        source = (
            'import std;import math;\n'
            '// A global value.\n'
            'let count=1;let total=2;\n'
            '// A function.\n'
            'fn first(){} // Keep this with first.\n'
            '/* A second function. */\n'
            'fn second(){}'
        )
        self.assertEqual(self.assert_preserved(source), (
            'import std;\n'
            'import math;\n'
            '\n'
            '// A global value.\n'
            'let count = 1;\n'
            'let total = 2;\n'
            '\n'
            '// A function.\n'
            'fn first() {} // Keep this with first.\n'
            '\n'
            '/* A second function. */\n'
            'fn second() {}\n'
        ))

    def test_binary_operators_and_prefixes(self):
        result = self.assert_preserved(
            'fn f(){let mask=bits<<shift;let high=bits>>2;'
            'assert(count<10&&count>0);let set=flags&3;'
            'assert(! enabled);let inverse=~ bits;assert(!!enabled);'
            'let ref=& value;}'
        )
        self.assertIn('let mask = bits << shift;', result)
        self.assertIn('let high = bits >> 2;', result)
        self.assertIn('assert(count < 10 && count > 0);', result)
        self.assertIn('let set = flags & 3;', result)
        self.assertIn('assert(!enabled);', result)
        self.assertIn('let inverse = ~bits;', result)
        self.assertIn('assert(!!enabled);', result)
        self.assertIn('let ref = &value;', result)

    def test_type_punctuation_and_separate_generic_closers(self):
        result = self.assert_preserved(
            'struct Box<T>{value:T}\n'
            'fn f(x:Box<Box<i64> >&?,y:i64[>..]&){'
            'let object=Box<Box<i64>>{value:Box<i64>{value:1}};}'
        )
        self.assertIn('x: Box<Box<i64> >&?', result)
        self.assertIn('y: i64[>..]&', result)
        self.assertIn('Box<Box<i64>> {', result)

    def test_cast_marker_and_logical_not_have_distinct_spacing(self):
        source = (
            'fn f() { let x = a as! i64; let y = !ready; '
            'let narrowed = bytes as ! const u8[:]; '
            'let checked = value as const u8[:]; }'
        )
        self.assertEqual(self.assert_preserved(source), (
            'fn f() {\n'
            '    let x = a as! i64;\n'
            '    let y = !ready;\n'
            '    let narrowed = bytes as! const u8[:];\n'
            '    let checked = value as const u8[:];\n'
            '}\n'
        ))

    def test_literals_and_nested_comments_are_exact(self):
        source = (
            'fn main(){/* outer /* inner */ end */\n'
            'print("// { \\\" }", \'\\x41\', """raw \\n { }""");\n'
            'print("""\n  a\n\n \n  b\n  """); // keep  two spaces  \n'
            '}\n'
        )
        self.assert_preserved(source)

    def test_numeric_boundaries_and_operators(self):
        source = (
            'fn f(){let x=0x1.8p+3;let y=1e-4;let z=18446744073709551615;'
            'let a=[1;3];let r=1..2;let b=x- -y;let c=x / /* why */ y;'
            'x<<=2;x.=y;assert(x.==y);}\n'
        )
        result = self.assert_preserved(source)
        self.assertIn('let a = [1; 3];', result)
        self.assertIn('let b = x - -y;', result)
        self.assertIn('x <<= 2;', result)

    def test_generic_and_reference_punctuation(self):
        self.assert_preserved(
            'struct Box<T>{x:T}\n'
            'fn f<T>(x:Box<Box<T> >&,y:T&<in x>) { '
            'let p=Box<Box<T>> {x:Box<T>{x:y}};'
            'assert(a<lim::COUNT);assert(b >> 1 > 0);}\n'
        )

    def test_match_pattern_lists_stay_together(self):
        result = self.assert_preserved(
            'fn f(x){match x {0,1,3..5=>7,6,8=>9,_=>0}}\n'
        )
        self.assertIn('        0, 1, 3..5 => 7,\n', result)
        self.assertIn('        6, 8 => 9,\n', result)

    def test_else_and_postfix_after_block(self):
        result = self.assert_preserved(
            'fn f(){let x=if c{1}else{2};print((if c{1}else{2})+3);}\n'
        )
        self.assertIn('} else {', result)
        self.assertIn('    };\n', result)
        self.assertIn('}) + 3);', result)

    def test_malformed_sources_fail(self):
        for source in ('/* missing', '"missing', "'ab'", '"\\q"',
                       '"""\n x\n y"""', '"""\n x\n  """',
                       '"""text\n"""', '0x', '0x1.2', '0x1p+',
                       'fn f(){', 'let x=];', '@', '\x00'):
            with self.subTest(source=source):
                with self.assertRaises(formatter.FormatError):
                    formatter.format_source(source)

    def test_bom_crlf_and_blank_lines(self):
        result = self.assert_preserved('\ufeffimport std;\r\n\r\nfn f(){\r\n}\r\n')
        self.assertTrue(result.startswith('\ufeffimport std;\n\n'))
        self.assertEqual(formatter.format_source(' \n\t'), '')

    def test_blank_lines_preserve_statement_groups(self):
        source = (
            'fn main() {\n'
            '    let first = 1;\n'
            '\n'
            '    // The second group has a separate purpose.\n'
            '    print(first);\n'
            '\n'
            '    let second = 2;\n'
            '    print(second);\n'
            '}\n'
        )
        self.assertEqual(self.assert_preserved(source), source)

    def test_check_and_write(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'sample.goose'
            path.write_text('fn f(){print(1);}\n', encoding='utf-8')
            checked = subprocess.run([sys.executable, SCRIPT, '--check', path],
                                     capture_output=True, text=True)
            self.assertEqual(checked.returncode, 1, checked.stderr)
            self.assertEqual(path.read_text(), 'fn f(){print(1);}\n')
            written = subprocess.run([sys.executable, SCRIPT, path],
                                     capture_output=True, text=True)
            self.assertEqual(written.returncode, 0, written.stderr)
            checked = subprocess.run([sys.executable, SCRIPT, '--check', path],
                                     capture_output=True, text=True)
            self.assertEqual(checked.returncode, 0, checked.stderr)

    def test_invalid_file_prevents_all_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            valid = Path(directory) / 'valid.goose'
            invalid = Path(directory) / 'invalid.goose'
            valid.write_text('fn f(){}', encoding='utf-8')
            invalid.write_text('/* missing', encoding='utf-8')
            result = subprocess.run([sys.executable, SCRIPT, valid, invalid],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('unterminated', result.stderr)
            self.assertEqual(valid.read_text(), 'fn f(){}')

    def test_changed_since_selects_valid_fixtures(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            def git(*args):
                subprocess.run(['git', *args], cwd=repo, check=True,
                               capture_output=True)
            git('init', '-q')
            git('config', 'user.name', 'Formatter test')
            git('config', 'user.email', 'formatter@example.invalid')
            for name in ('test/errors/bad.goose', 'test/errors_tc/valid.goose',
                         'space name.goose'):
                path = repo / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('fn f() {}\n')
            git('add', '.')
            git('commit', '-qm', 'initial')
            (repo / 'test/errors/bad.goose').write_text('/* malformed')
            (repo / 'test/errors_tc/valid.goose').write_text('fn f(){}')
            (repo / 'space name.goose').write_text('fn f(){}')
            result = subprocess.run(
                [sys.executable, SCRIPT, '--changed-since', 'HEAD'], cwd=repo,
                capture_output=True, text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((repo / 'test/errors/bad.goose').read_text(), '/* malformed')
            self.assertEqual((repo / 'space name.goose').read_text(), 'fn f() {}\n')
            failed = subprocess.run(
                [sys.executable, SCRIPT, '--check', '--changed-since', 'no-such-ref'],
                cwd=repo, capture_output=True, text=True,
            )
            self.assertEqual(failed.returncode, 2)


if __name__ == '__main__':
    unittest.main()
