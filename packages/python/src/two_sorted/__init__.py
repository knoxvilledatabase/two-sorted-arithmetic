"""
two-sorted — Origin | Bounded type system

Replaces None, NaN with one concept.
Formally verified in Lean 4. 260 theorems. Zero sorry's.

https://github.com/knoxvilledatabase/two-sorted-arithmetic
"""

from __future__ import annotations
from typing import TypeVar, Callable, Union, Any
import math

T = TypeVar("T")
U = TypeVar("U")
R = TypeVar("R")


class _OriginType:
    """The categorical origin. Not a value. The boundary condition of all values."""
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __repr__(self) -> str:
        return "𝒪"

    def __bool__(self) -> bool:
        return False

    def __eq__(self, other: object) -> bool:
        return isinstance(other, _OriginType)

    def __hash__(self) -> int:
        return hash("𝒪")


Origin = _OriginType()
"""The categorical origin. Not a value. The boundary condition of all values."""

Zero = Union[_OriginType, T]
"""The two-sorted type: either Origin (no container) or T (the value itself)."""


def from_nullable(value: T | None) -> Zero[T]:
    """Convert a nullable value. None/NaN → Origin.
    Origin means the container doesn't exist — not that it's empty."""
    if value is None:
        return Origin
    if isinstance(value, float) and math.isnan(value):
        return Origin
    return value


def op(f: Callable[[T, U], R], a: Zero[T], b: Zero[U]) -> Zero[R]:
    """Apply f to two Zero values.
    If either is Origin, result is Origin. (I1, I2, I3)
    If both are values, apply f."""
    if a is Origin:
        return Origin
    if b is Origin:
        return Origin
    return f(a, b)  # type: ignore


def chain(f: Callable[[T], Zero[U]], a: Zero[T]) -> Zero[U]:
    """Chain Zero-returning operations. Like flatMap/bind.
    If Origin, short-circuits. If value, apply the function."""
    if a is Origin:
        return Origin
    return f(a)  # type: ignore


__all__ = [
    "Origin",
    "Zero",
    "from_nullable",
    "op",
    "chain",
]
