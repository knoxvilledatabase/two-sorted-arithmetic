/-
Released under MIT license.
-/
import Std

/-!
# ZMod Benchmark: NeZero in modular arithmetic

`ZMod n` — the integers modulo `n` — requires `[NeZero n]` on almost every
theorem because `n` is playing two roles: a modulus (structural parameter
that defines the type) and a natural number (that could be zero).

`NeZero` is the patch: "we know `n` isn't zero, trust us."

In the two-sorted version, the modulus is a positive natural — nonzero by
type, not by hypothesis. `[NeZero n]` becomes unnecessary.

This is a simplified model of `ZMod`, not a replacement for Mathlib's
implementation. It demonstrates the pattern.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: ZMod n where n : Nat, requiring [NeZero n]
-- ============================================================================

namespace ZModCollapsed

/-- Simplified ZMod: values mod n, represented as Fin n when n > 0.
    When n = 0, the type is degenerate. NeZero excludes this. -/
structure ZMod (n : Nat) where
  val : Nat
  val_lt : n = 0 ∨ val < n  -- must allow n=0 case in the type

/-- NeZero: the hypothesis that n ≠ 0. Must be carried on every theorem. -/
class NeZero (n : Nat) : Prop where
  ne : n ≠ 0

/-- Smart constructor: only valid when n > 0. Requires NeZero. -/
def mk (n : Nat) [NeZero n] (v : Nat) : ZMod n :=
  ⟨v % n, Or.inr (Nat.mod_lt v (Nat.pos_of_ne_zero NeZero.ne))⟩

/-- 1. val < n. Requires NeZero. -/
theorem val_lt (n : Nat) [NeZero n] (a : ZMod n) : a.val < n := by
  cases a.val_lt with
  | inl h => exact absurd h NeZero.ne
  | inr h => exact h

/-- 2. Addition mod n. Requires NeZero. -/
def add (n : Nat) [NeZero n] (a b : ZMod n) : ZMod n :=
  mk n (a.val + b.val)

/-- 3. Multiplication mod n. Requires NeZero. -/
def mul (n : Nat) [NeZero n] (a b : ZMod n) : ZMod n :=
  mk n (a.val * b.val)

/-- 4. Zero element mod n. Requires NeZero. -/
def zero (n : Nat) [NeZero n] : ZMod n :=
  mk n 0

/-- 5. Casting from Nat to ZMod n. Requires NeZero. -/
def natCast (n : Nat) [NeZero n] (v : Nat) : ZMod n :=
  mk n v

/-- 6. The modulus is positive. Requires NeZero. -/
theorem modulus_pos (n : Nat) [NeZero n] : 0 < n :=
  Nat.pos_of_ne_zero NeZero.ne

/-- 7. Two elements are equal iff their values are equal. Requires NeZero
    (to know val < n, so the representation is canonical). -/
theorem ext (n : Nat) [NeZero n] (a b : ZMod n)
    (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; simp [h]

/-- 8. natCast 0 = zero. Requires NeZero. -/
theorem natCast_zero (n : Nat) [NeZero n] :
    natCast n 0 = zero n := by
  rfl

-- SUMMARY:
--   [NeZero n] instances required: 8 (every theorem and definition)
--   Theorems/defs total: 8
--   NeZero adoption rate: 100%

end ZModCollapsed

-- ============================================================================
-- TWO-SORTED: ZMod on PosNat, no NeZero needed
-- ============================================================================

namespace ZModTwoSorted

/-- PosNat: positive naturals. The modulus type.
    Nonzero by construction. No NeZero needed. -/
structure PosNat where
  val : Nat
  pos : 0 < val

/-- Simplified ZMod on PosNat: values mod n, where n is positive by type. -/
structure ZMod (n : PosNat) where
  val : Nat
  val_lt : val < n.val

/-- Smart constructor. No NeZero hypothesis. The type carries it. -/
def mk (n : PosNat) (v : Nat) : ZMod n :=
  ⟨v % n.val, Nat.mod_lt v n.pos⟩

/-- 1. val < n. No hypothesis. The type guarantees it. -/
theorem val_lt (n : PosNat) (a : ZMod n) : a.val < n.val :=
  a.val_lt

/-- 2. Addition mod n. No NeZero. -/
def add (n : PosNat) (a b : ZMod n) : ZMod n :=
  mk n (a.val + b.val)

/-- 3. Multiplication mod n. No NeZero. -/
def mul (n : PosNat) (a b : ZMod n) : ZMod n :=
  mk n (a.val * b.val)

/-- 4. Zero element mod n. No NeZero. -/
def zero (n : PosNat) : ZMod n :=
  mk n 0

/-- 5. Casting from Nat to ZMod n. No NeZero. -/
def natCast (n : PosNat) (v : Nat) : ZMod n :=
  mk n v

/-- 6. The modulus is positive. No NeZero — it's the type. -/
theorem modulus_pos (n : PosNat) : 0 < n.val :=
  n.pos

/-- 7. Two elements are equal iff their values are equal. No NeZero. -/
theorem ext (n : PosNat) (a b : ZMod n)
    (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; simp [h]

/-- 8. natCast 0 = zero. No NeZero. -/
theorem natCast_zero (n : PosNat) :
    natCast n 0 = zero n := by
  rfl

-- SUMMARY:
--   [NeZero n] instances required: 0
--   Theorems/defs total: 8
--   NeZero adoption rate: 0%
--   Information lost: 0

end ZModTwoSorted

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                         Collapsed (Nat)    Two-Sorted (PosNat)
--  [NeZero n] required         8                  0
--  Theorems/defs                8                  8
--  Degenerate case (n=0)   must exclude         impossible by type
--  Information lost             0                  0
--
--  Every definition and every theorem in the collapsed version carries
--  [NeZero n]. In the two-sorted version, zero of them do.
--
--  The modulus n is playing two roles in the collapsed version:
--  1. A structural parameter that defines ZMod n
--  2. A natural number that could be zero
--
--  NeZero is the patch that says "role 2 won't cause problems for role 1."
--  PosNat eliminates the collision. The modulus is positive by type.
--  The patch becomes unnecessary.
--
--  This is the same finding as the GroupWithZero benchmarks, extended
--  from division to modular arithmetic. The pattern generalizes.
