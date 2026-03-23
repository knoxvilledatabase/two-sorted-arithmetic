import { Origin, from, op, chain, Zero } from "./index";

// ---------------------------------------------------------------------------
// Core
// ---------------------------------------------------------------------------

describe("Core", () => {
  test("Origin is a symbol", () => {
    expect(typeof Origin).toBe("symbol");
  });

  test("Origin !== any value", () => {
    expect(Origin).not.toBe(0);
    expect(Origin).not.toBe("");
    expect(Origin).not.toBe(false);
  });
});

// ---------------------------------------------------------------------------
// from
// ---------------------------------------------------------------------------

describe("from", () => {
  test("null → Origin", () => {
    expect(from(null)).toBe(Origin);
  });

  test("undefined → Origin", () => {
    expect(from(undefined)).toBe(Origin);
  });

  test("NaN → Origin", () => {
    expect(from(NaN)).toBe(Origin);
  });

  test("0 → 0", () => {
    expect(from(0)).toBe(0);
  });

  test("empty string → empty string (empty container, not Origin)", () => {
    expect(from("")).toBe("");
  });

  test("false → false (a value, not Origin)", () => {
    expect(from(false)).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// op — Interaction Axioms (I1–I3)
// ---------------------------------------------------------------------------

describe("op", () => {
  const add = (a: number, b: number) => a + b;

  test("I1: f(x, Origin) = Origin", () => {
    expect(op(add, 1, Origin)).toBe(Origin);
  });

  test("I2: f(Origin, x) = Origin", () => {
    expect(op(add, Origin, 1)).toBe(Origin);
  });

  test("I3: f(Origin, Origin) = Origin", () => {
    expect(op(add, Origin, Origin)).toBe(Origin);
  });

  test("f(x, y) when both values", () => {
    expect(op(add, 2, 3)).toBe(5);
  });
});

// ---------------------------------------------------------------------------
// chain
// ---------------------------------------------------------------------------

describe("chain", () => {
  const safeDivide = (x: number): Zero<number> =>
    x === 0 ? Origin : 100 / x;

  test("chains values", () => {
    expect(chain(safeDivide, 4)).toBe(25);
  });

  test("chain to Origin propagates", () => {
    expect(chain(safeDivide, 0)).toBe(Origin);
  });

  test("Origin input short-circuits", () => {
    expect(chain(safeDivide, Origin)).toBe(Origin);
  });
});

// ---------------------------------------------------------------------------
// Real-world: pipeline via chain
// ---------------------------------------------------------------------------

describe("Real-world: API pipeline", () => {
  const fetchUser = (id: number): Zero<{ name: string; balanceId: number }> =>
    id > 0 ? { name: "Alice", balanceId: 42 } : Origin;

  const fetchBalance = (balanceId: number): Zero<number> =>
    balanceId > 0 ? 1000 : Origin;

  const computeTax = (balance: number): Zero<number> =>
    balance >= 0 ? balance * 0.2 : Origin;

  test("valid pipeline completes", () => {
    const result = chain(
      (user) => chain(
        (balance) => computeTax(balance),
        fetchBalance(user.balanceId)
      ),
      fetchUser(1)
    );
    expect(result).toBe(200);
  });

  test("invalid user → Origin propagates", () => {
    const result = chain(
      (user) => chain(
        (balance) => computeTax(balance),
        fetchBalance(user.balanceId)
      ),
      fetchUser(-1)
    );
    expect(result).toBe(Origin);
  });
});
