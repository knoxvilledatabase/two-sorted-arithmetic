/**
 * two-sorted — Origin | Bounded type system
 *
 * Replaces null, undefined, NaN with one concept.
 * Formally verified in Lean 4. 260 theorems. Zero sorry's.
 *
 * https://github.com/knoxvilledatabase/two-sorted-arithmetic
 */

/** The categorical origin. Not a value. The boundary condition of all values. */
const _Origin = Symbol.for("𝒪");
export type Origin = typeof _Origin;
export const Origin: Origin = _Origin;

/** The two-sorted type: either Origin (no container) or T (the value itself). */
export type Zero<T> = Origin | T;

/** Convert a nullable value. null/undefined/NaN → Origin.
 *  Origin means the container doesn't exist — not that it's empty. */
export function from<T>(value: T | null | undefined): Zero<T> {
  if (value === null || value === undefined) return Origin;
  if (typeof value === "number" && Number.isNaN(value)) return Origin;
  return value;
}

/** Apply a function to two Zero values.
 *  If either is Origin, the result is Origin. (I1, I2, I3)
 *  If both are values, apply the function. */
export function op<A, B, C>(
  f: (a: A, b: B) => C,
  a: Zero<A>,
  b: Zero<B>
): Zero<C> {
  if (a === Origin) return Origin;
  if (b === Origin) return Origin;
  return f(a as A, b as B);
}

/** Chain Zero-returning operations. Like flatMap/bind.
 *  If Origin, short-circuits. If value, apply the function. */
export function chain<A, B>(f: (a: A) => Zero<B>, a: Zero<A>): Zero<B> {
  if (a === Origin) return Origin;
  return f(a as A);
}
