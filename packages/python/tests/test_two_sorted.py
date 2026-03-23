import pytest
from two_sorted import Origin, from_nullable, op, chain


# ---------------------------------------------------------------------------
# Core
# ---------------------------------------------------------------------------

class TestCore:
    def test_origin_is_singleton(self):
        from two_sorted import _OriginType
        assert _OriginType() is _OriginType()

    def test_origin_repr(self):
        assert repr(Origin) == "𝒪"

    def test_origin_is_falsy(self):
        assert not Origin


# ---------------------------------------------------------------------------
# from_nullable
# ---------------------------------------------------------------------------

class TestFromNullable:
    def test_none_to_origin(self):
        assert from_nullable(None) is Origin

    def test_nan_to_origin(self):
        assert from_nullable(float("nan")) is Origin

    def test_zero_to_zero(self):
        assert from_nullable(0) == 0

    def test_empty_string_stays(self):
        """Empty string is an empty container, not Origin."""
        assert from_nullable("") == ""

    def test_false_stays(self):
        """False is a value, not Origin."""
        assert from_nullable(False) is not Origin


# ---------------------------------------------------------------------------
# op — Interaction Axioms (I1–I3)
# ---------------------------------------------------------------------------

class TestOp:
    def test_i1(self):
        assert op(lambda a, b: a + b, 1, Origin) is Origin

    def test_i2(self):
        assert op(lambda a, b: a + b, Origin, 1) is Origin

    def test_i3(self):
        assert op(lambda a, b: a + b, Origin, Origin) is Origin

    def test_both_values(self):
        assert op(lambda a, b: a + b, 2, 3) == 5


# ---------------------------------------------------------------------------
# chain
# ---------------------------------------------------------------------------

class TestChain:
    def test_chains_values(self):
        safe_div = lambda x: Origin if x == 0 else 100 / x
        assert chain(safe_div, 4) == 25.0

    def test_chain_to_origin(self):
        safe_div = lambda x: Origin if x == 0 else 100 / x
        assert chain(safe_div, 0) is Origin

    def test_origin_short_circuits(self):
        safe_div = lambda x: Origin if x == 0 else 100 / x
        assert chain(safe_div, Origin) is Origin


# ---------------------------------------------------------------------------
# Real-world: pipeline via chain
# ---------------------------------------------------------------------------

class TestRealWorld:
    def test_valid_pipeline(self):
        fetch_user = lambda id: {"name": "Alice", "balance_id": 42} if id > 0 else Origin
        fetch_balance = lambda bid: 1000 if bid > 0 else Origin
        compute_tax = lambda bal: bal * 0.2 if bal >= 0 else Origin

        result = chain(
            lambda user: chain(
                lambda bal: compute_tax(bal),
                fetch_balance(user["balance_id"])
            ),
            fetch_user(1)
        )
        assert result == 200.0

    def test_invalid_user_propagates(self):
        fetch_user = lambda id: {"name": "Alice", "balance_id": 42} if id > 0 else Origin
        fetch_balance = lambda bid: 1000 if bid > 0 else Origin
        compute_tax = lambda bal: bal * 0.2 if bal >= 0 else Origin

        result = chain(
            lambda user: chain(
                lambda bal: compute_tax(bal),
                fetch_balance(user["balance_id"])
            ),
            fetch_user(-1)
        )
        assert result is Origin
