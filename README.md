# Pascal Minus-One GCD

Lean/Mathlib formalisation of the restricted binomial gcd

\[
G(N;m)=\gcd\{\binom Nk:0<k<N,\ m\mid k\},
\]

with immediate focus on primes `p ≡ -1 (mod m)`.

## Target theorem

Assume `m ≥ 3`, `m ∣ N`, `N > m`, `p` prime, and `p ≡ -1 (mod m)`. Write the base-`p` expansion `N = Σ d_i p^i`, and set

- `A = Σ_{i even} d_i`,
- `B = Σ_{i odd} d_i`.

The target valuation is

- `2` for `(A,B)=(1,1)` and `p=m-1`;
- `1` for `(A,B)=(1,1)` and `p>m`;
- `1` for `(A,B)=(m,0)` or `(0,m)`;
- `0` otherwise.

The Lean theorem is named `PascalMinusOne.minus_one_valuation`.

## Current status

The proof-formalisation core is complete on the current proof branch. Both `PascalMinusOne.minus_one_valuation` and `PascalMinusOne.scaling_valuation` are fully proved, and the repository contains **0 explicit `sorry` occurrences**. CI enforces the zero-`sorry` count alongside `lake build`, the Python regression tests, and the independent reference sweep.

The next formal layer is the advertised `m = 3,4,6` corollaries in `PascalMinusOne/SmallModuli.lean`. Those corollaries are not yet stated as verified; their exact scope must respect the existing literature boundary and whatever plus-one branch is formally available.

## Layout

- `PascalMinusOne/Basic.lean`: admissible indices and `G`.
- `PascalMinusOne/Digits.lean`: base-`p` parity digit sums.
- `PascalMinusOne/Kummer.lean`: Mathlib Kummer wrapper and proved zero-borrow/digitwise bridge.
- `PascalMinusOne/SignedTokens.lean`: reusable `±1` zero-sum layer.
- `PascalMinusOne/MinusOne.lean`: branch lemmas and main theorem.
- `PascalMinusOne/Scaling.lean`: trailing-zero scaling theorem.
- `PascalMinusOne/SmallModuli.lean`: future `m=3,4,6` corollaries.
- `scripts/reference_check.py`: independent finite regression checker.
- `tests/test_reference_checker.py`: Python regression tests.
- `notes/`: proof architecture, literature boundary, discovery provenance.

## Build and test

The project pins Mathlib to commit `bd6c1abe5f55b6c3856172d6a23703e0888f5286` and Lean `v4.35.0-rc2`.

```bash
lake update
lake build
python3 -m unittest discover -s tests -v
python3 scripts/reference_check.py
```

The Python checks are regression evidence only. The proof status is determined by Lean and by elimination of all documented `sorry` placeholders.

## Mathlib findings

The key existing theorem is `padicValNat_choose` in `Mathlib.NumberTheory.Padics.PadicVal.Basic`, documented there as Kummer's theorem: the `p`-adic valuation of `n.choose k` is the number of base-`p` carries in `k + (n-k)`. Mathlib also contains `Nat.Prime.multiplicity_choose` and extensive `Nat.digits` lemmas.

## Literature

See `notes/literature.md`. Novelty is promising but **not established**; no novelty claim should be made without a dedicated source-level literature pass.

## License

No license has been selected yet. Add one deliberately before public distribution.
