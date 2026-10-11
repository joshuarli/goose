"""Shared observable contracts returned by semantic-lane evaluators."""

from dataclasses import dataclass


@dataclass(frozen=True)
class RejectExpectation:
    """Stable diagnostic fragments required from a clean compiler rejection."""

    diagnostic_contains: tuple[str, ...]
