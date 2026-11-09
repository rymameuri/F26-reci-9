import { describe, expect, it } from 'vitest';
import fc from 'fast-check';
import { mergeIntervals, type Interval } from '../src/intervals';

// Read the spec in src/intervals/mergeIntervals.ts, then check your progress
// with `npm run mutants:intervals`.
//
// Label every property with its pattern, on the line above its `it(`:
//   // Pattern: invariant. The output is sorted.
// (invariant, algebraic, metamorphic, differential, or conditional)

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

// Checkpoint 1: the first-draft generator, fc.tuple(fc.integer(), fc.integer()),
// produced invalid intervals such as [0, -1] (start > end), which the spec says
// must throw a RangeError. So the property failed on the correct code.
// Fix: build valid intervals by construction, as a start plus a non-negative
// length. Never filter.
//
// Checkpoint 3: endpoints drawn from all 32-bit integers almost never coincide,
// so bugs about intervals that touch ([1, 3] + [3, 5]), sit exactly one apart
// ([1, 2] + [3, 4]), nest, or repeat would never be reached. Most intervals
// therefore come from a small window, where those cases are common; some come
// from a wide range so multi-digit and negative numbers (sorting) still show up.
const smallInterval: fc.Arbitrary<Interval> = fc
  .tuple(fc.integer({ min: -10, max: 10 }), fc.nat(6))
  .map(([start, len]): Interval => [start, start + len]);

const wideInterval: fc.Arbitrary<Interval> = fc
  .tuple(fc.integer({ min: -1_000_000, max: 1_000_000 }), fc.nat(1_000_000))
  .map(([start, len]): Interval => [start, start + len]);

const interval: fc.Arbitrary<Interval> = fc.oneof(
  { weight: 5, arbitrary: smallInterval },
  { weight: 1, arbitrary: wideInterval },
);

const intervalList = fc.array(interval, { maxLength: 12 });

// Already-disjoint input, built directly (targeted generator, no filtering):
// walk left to right, leaving a gap of at least 1 between intervals so that no
// two of them overlap or touch. Gap 1 is common, e.g. [1, 2] and [3, 4], which
// must stay separate. The order is then shuffled.
const disjointSorted: fc.Arbitrary<Interval[]> = fc
  .tuple(
    fc.integer({ min: -50, max: 50 }),
    fc.array(fc.tuple(fc.integer({ min: 1, max: 4 }), fc.nat(4)), { maxLength: 10 }),
  )
  .map(([origin, pieces]) => {
    const out: Interval[] = [];
    let cursor = origin;
    for (const [gap, len] of pieces) {
      const start = cursor + gap;
      out.push([start, start + len]);
      cursor = start + len;
    }
    return out;
  });

const disjointShuffled: fc.Arbitrary<{ sorted: Interval[]; input: Interval[] }> =
  disjointSorted.chain(sorted =>
    fc
      .shuffledSubarray(sorted, { minLength: sorted.length, maxLength: sorted.length })
      .map(input => ({ sorted, input })),
  );

// An invalid interval: start > end, or a non-integer / non-finite endpoint.
const invalidInterval: fc.Arbitrary<[number, number]> = fc.oneof(
  fc
    .tuple(fc.integer({ min: -20, max: 20 }), fc.integer({ min: 1, max: 5 }))
    .map(([end, d]): [number, number] => [end + d, end]),
  fc
    .tuple(fc.integer({ min: -20, max: 20 }), fc.nat(5))
    .map(([s, len]): [number, number] => [s + 0.5, s + len + 1]),
  fc
    .tuple(fc.integer({ min: -20, max: 20 }), fc.nat(5))
    .map(([s, len]): [number, number] => [s, s + len + 0.5]),
  fc.constantFrom<[number, number]>(
    [Number.NaN, 0],
    [0, Number.NaN],
    [0, Number.POSITIVE_INFINITY],
    [Number.NEGATIVE_INFINITY, 0],
  ),
);

// ---------------------------------------------------------------------------
// Helpers (small oracles, not a re-implementation)
// ---------------------------------------------------------------------------

const clone = (xs: readonly Interval[]): Interval[] => xs.map(([s, e]): Interval => [s, e]);

/** Is the real number p inside at least one closed interval? */
const covers = (xs: readonly Interval[], p: number): boolean =>
  xs.some(([s, e]) => s <= p && p <= e);

/** Points worth probing: every endpoint, plus points just inside/outside it. */
const probePoints = (xs: readonly Interval[]): number[] => {
  const pts = new Set<number>();
  for (const [s, e] of xs) {
    for (const x of [s, e]) {
      for (const d of [-1, -0.5, 0, 0.5, 1]) pts.add(x + d);
    }
  }
  return [...pts];
};

const sortByStart = (xs: readonly Interval[]): Interval[] =>
  [...xs].sort((a, b) => a[0] - b[0] || a[1] - b[1]);

// ---------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------

describe('mergeIntervals', () => {
  // Pattern: invariant. Every input interval lies inside some output interval.
  it('every input interval lies inside some output interval', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const uncovered = xs.filter(([s, e]) => !out.some(([a, b]) => a <= s && e <= b));
        expect(uncovered).toEqual([]);
      }),
    );
  });

  // Pattern: invariant. The output is made of valid intervals, sorted by start, and consecutive intervals neither overlap nor touch.
  it('returns valid, sorted intervals with a real gap between neighbours', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        for (const [s, e] of out) {
          expect(Number.isInteger(s) && Number.isInteger(e)).toBe(true);
          expect(s).toBeLessThanOrEqual(e);
        }
        for (let i = 0; i + 1 < out.length; i++) {
          expect(out[i][1]).toBeLessThan(out[i + 1][0]);
        }
      }),
    );
  });

  // Pattern: invariant. Output endpoints come from the input, and the output is never longer than the input.
  it('only uses endpoints from the input and never grows the list', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const out = mergeIntervals(xs);
        const starts = new Set(xs.map(([s]) => s));
        const ends = new Set(xs.map(([, e]) => e));
        expect(out.length).toBeLessThanOrEqual(xs.length);
        for (const [s, e] of out) {
          expect(starts.has(s)).toBe(true);
          expect(ends.has(e)).toBe(true);
        }
      }),
    );
  });

  // Pattern: invariant. The input array and the intervals in it are not modified.
  it('does not modify its input', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const before = clone(xs);
        const inputArray = xs;
        const inputItems = [...xs];
        const out = mergeIntervals(xs);
        expect(xs).toEqual(before);
        expect(xs).toBe(inputArray);
        inputItems.forEach((iv, i) => expect(iv).toBe(xs[i]));
        // Changing the output must not reach back into the input.
        for (const iv of out) {
          iv[0] -= 1000;
          iv[1] += 1000;
        }
        expect(xs).toEqual(before);
      }),
    );
  });

  // Pattern: differential. A point is covered by the output exactly when it is covered by the input (checked at, between and around every endpoint).
  it('covers exactly the same points as the input', () => {
    fc.assert(
      fc.property(intervalList, fc.double({ min: -30, max: 30, noNaN: true }), (xs, extra) => {
        const out = mergeIntervals(xs);
        for (const p of [...probePoints(xs), ...probePoints(out), extra]) {
          expect({ p, covered: covers(out, p) }).toEqual({ p, covered: covers(xs, p) });
        }
      }),
    );
  });

  // Pattern: metamorphic. Reordering the input does not change the output.
  it('does not depend on the order of the input', () => {
    fc.assert(
      fc.property(
        intervalList.chain(xs =>
          fc
            .shuffledSubarray(xs, { minLength: xs.length, maxLength: xs.length })
            .map(ys => [xs, ys] as const),
        ),
        ([xs, ys]) => {
          expect(mergeIntervals(clone(ys))).toEqual(mergeIntervals(clone(xs)));
        },
      ),
    );
  });

  // Pattern: metamorphic. Adding duplicates of intervals already in the input does not change the output.
  it('ignores duplicated intervals', () => {
    fc.assert(
      fc.property(
        intervalList.chain(xs =>
          fc.shuffledSubarray(xs).map(dups => [xs, [...xs, ...clone(dups)]] as const),
        ),
        ([xs, withDups]) => {
          expect(mergeIntervals(withDups)).toEqual(mergeIntervals(xs));
        },
      ),
    );
  });

  // Pattern: metamorphic. Shifting every input interval by k shifts every output interval by k.
  it('commutes with translation', () => {
    fc.assert(
      fc.property(intervalList, fc.integer({ min: -100, max: 100 }), (xs, k) => {
        const shifted = xs.map(([s, e]): Interval => [s + k, e + k]);
        const expected = mergeIntervals(xs).map(([s, e]): Interval => [s + k, e + k]);
        expect(mergeIntervals(shifted)).toEqual(expected);
      }),
    );
  });

  // Pattern: metamorphic. Adding an interval that lies inside an existing input interval does not change the output.
  it('ignores intervals nested inside existing ones', () => {
    fc.assert(
      fc.property(
        fc
          .array(interval, { minLength: 1, maxLength: 12 })
          .chain(xs =>
            fc
              .tuple(fc.nat(xs.length - 1), fc.nat(), fc.nat())
              .map(([i, a, b]) => {
                const [s, e] = xs[i];
                const lo = s + (a % (e - s + 1));
                const hi = lo + (b % (e - lo + 1));
                return [xs, [...xs, [lo, hi] as Interval]] as const;
              }),
          ),
        ([xs, more]) => {
          expect(mergeIntervals(more)).toEqual(mergeIntervals(xs));
        },
      ),
    );
  });

  // Pattern: algebraic. Merging is idempotent: merging an already merged list gives it back unchanged.
  it('is idempotent', () => {
    fc.assert(
      fc.property(intervalList, xs => {
        const once = mergeIntervals(xs);
        expect(mergeIntervals(clone(once))).toEqual(once);
      }),
    );
  });

  // Pattern: algebraic. Merging two lists separately and then together equals merging their concatenation.
  it('merge(a ++ b) = merge(merge(a) ++ merge(b))', () => {
    fc.assert(
      fc.property(intervalList, intervalList, (a, b) => {
        const whole = mergeIntervals([...clone(a), ...clone(b)]);
        const parts = mergeIntervals([...mergeIntervals(a), ...mergeIntervals(b)]);
        expect(parts).toEqual(whole);
      }),
    );
  });

  // Pattern: conditional. If the input intervals already neither overlap nor touch, the output is exactly those intervals, sorted by start.
  it('returns already-disjoint input unchanged apart from sorting', () => {
    fc.assert(
      fc.property(disjointShuffled, ({ sorted, input }) => {
        expect(mergeIntervals(input)).toEqual(sorted);
      }),
    );
  });

  // Pattern: conditional. If two intervals overlap or touch, they become a single interval spanning both.
  it('merges two intervals that overlap or touch into one', () => {
    fc.assert(
      fc.property(
        fc
          .tuple(smallInterval, fc.nat(), fc.nat(6))
          .map(([[s, e], off, len]): [Interval, Interval] => {
            const start2 = s + (off % (e - s + 1)); // start2 is in [s, e]: overlap or touch
            return [[s, e], [start2, start2 + len]];
          }),
        fc.boolean(),
        ([a, b], flip) => {
          const input = flip ? [b, a] : [a, b];
          expect(mergeIntervals(input)).toEqual([[a[0], Math.max(a[1], b[1])]]);
        },
      ),
    );
  });

  // Pattern: conditional. If any interval is invalid (start > end, or a non-integer endpoint), mergeIntervals throws a RangeError.
  it('throws a RangeError when any interval is invalid', () => {
    fc.assert(
      fc.property(intervalList, invalidInterval, fc.nat(), (xs, bad, pos) => {
        const input: Interval[] = [...xs];
        input.splice(pos % (xs.length + 1), 0, bad);
        expect(() => mergeIntervals(input)).toThrow(RangeError);
      }),
    );
  });

  // Example tests (do not count toward the required properties).
  it('handles the examples from the spec', () => {
    expect(mergeIntervals([])).toEqual([]);
    expect(mergeIntervals([[1, 3], [3, 5]])).toEqual([[1, 5]]);
    expect(mergeIntervals([[1, 2], [3, 4]])).toEqual([[1, 2], [3, 4]]);
    expect(mergeIntervals([[5, 5]])).toEqual([[5, 5]]);
  });
});
