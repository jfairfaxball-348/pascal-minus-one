# Pascal Minus-One GCD

Lean/Mathlib formalisation of the restricted binomial gcd

[
G(N;m)=gcdleft{inom Nk:0<k<N, mmid kight}.
]

The repository now formalises the `p ≡ -1 (mod m)` valuation theorem, the complementary
`p ≡ 1 (mod m)` branch needed by the project, the trailing-zero scaling reduction, and
complete prime-by-prime valuation formulas for `m = 3, 4, 6`.

## Formalised results

### Minus-one branch

Assume `m ≥ 3`, `m ∣ N`, `m < N`, `p` prime, and
`p % m = m - 1`. Write the base-`p` expansion of `N` as
`N = Σ d_i p^i`, and set

- `A = Σ_{i even} d_i`,
- `B = Σ_{i odd} d_i`.

Then the valuation is

- `2` for `(A,B)=(1,1)` and `p=m-1`;
- `1` for `(A,B)=(1,1)` and `p>m`;
- `1` for `(A,B)=(m,0)` or `(0,m)`;
- `0` otherwise.

The Lean theorem is `PascalMinusOne.minus_one_valuation`.

### Plus-one branch

Assume `0 < m`, `m ∣ N`, `m < N`, `p` prime, and
`p % m = 1 % m`. Then

[
v_p(G(N;m))=
egin{cases}
1,&	ext{if the base-}p	ext{ digit sum of }N	ext{ is }m,\
0,&	ext{otherwise.}
end{cases}
]

The formulation deliberately includes `m = 1` and `m = 2`, because those reduced
moduli occur after scaling in the small-modulus corollaries. The Lean theorem is
`PascalMinusOne.plus_one_valuation`.

### Scaling

For prime `p` and natural numbers `c,q,N'`,

[
v_p!left(G(p^cN';p^cq)ight)=v_p!left(G(N';q)ight).
]

This is `PascalMinusOne.scaling_valuation`.

### Complete formulas for `m = 3,4,6`

The public theorem layer contains

- `PascalMinusOne.modulus_three_valuation`,
- `PascalMinusOne.modulus_four_valuation`,
- `PascalMinusOne.modulus_six_valuation`.

Each theorem covers **every prime**. The cases are dispatched as follows:

| modulus | primes dividing the modulus | remaining primes |
| --- | --- | --- |
| `3` | `p=3`: scale to modulus `1`, then use the plus-one theorem | residues `1` or `-1` mod `3` |
| `4` | `p=2`: scale to modulus `1`, then use the plus-one theorem | residues `1` or `-1` mod `4` |
| `6` | `p=2`: scale to modulus `3`; `p=3`: scale to modulus `2` | residues `1` or `-1` mod `6` |

The corresponding piecewise right-hand sides are exposed as
`modulusThreeExpectedValuation`, `modulusFourExpectedValuation`, and
`modulusSixExpectedValuation`.

## Verification status

The advertised theorem layer is Lean-complete on the current proof branch. All of the
results above are proved without theorem placeholders. The project Lean sources contain
no `sorry`, `admit`, or replacement `axiom` declarations.

CI checks `lake build`, the Python regression suite, the independent finite reference
sweep, and an explicit zero-`sorry` gate. The computational checks are regression
evidence only; they are not used as substitutes for the infinite Lean proofs.

## Layout

- `PascalMinusOne/Basic.lean`: admissible indices, `G`, and gcd valuation infrastructure.
- `PascalMinusOne/Digits.lean`: base-`p` digit and parity-sum infrastructure.
- `PascalMinusOne/Kummer.lean`: Mathlib Kummer wrapper and zero-borrow/digitwise bridge.
- `PascalMinusOne/SignedTokens.lean`: reusable `±1` zero-sum layer.
- `PascalMinusOne/MinusOne.lean`: minus-one branch lemmas and `minus_one_valuation`.
- `PascalMinusOne/PlusOne.lean`: plus-one branch and `plus_one_valuation`.
- `PascalMinusOne/Scaling.lean`: trailing-zero scaling theorem.
- `PascalMinusOne/SmallModuli.lean`: complete `m=3,4,6` prime-by-prime corollaries.
- `scripts/reference_check.py`: independent finite regression checker.
- `tests/test_reference_checker.py`: Python regression tests.
- `notes/proof-outline.md`: proof architecture.
- `notes/literature.md`: concise literature boundary.
- `notes/novelty-audit-2026-09.md`: September 2026 source-level novelty audit.

## Build and test

The project pins Mathlib to commit
`bd6c1abe5f55b6c3856172d6a23703e0888f5286` and Lean `v4.35.0-rc2`.

```bash
lake update
lake build
python3 -m unittest discover -s tests -v
python3 scripts/reference_check.py
```

## Mathlib foundation

The central imported result is `padicValNat_choose` from
`Mathlib.NumberTheory.Padics.PadicVal.Basic`, Mathlib's Kummer theorem for the
`p`-adic valuation of binomial coefficients. The formalisation also uses Mathlib's
base-`p` digit and digit-sum lemmas.

## Literature and novelty

A source-level audit through **September 2026** located **no equivalent prior theorem
for the full `p ≡ -1 (mod m)` valuation formula**.

The closest prior art is Carl McTague's 2017 theorem for the same restricted gcd family.
McTague's `p ≡ 1 (mod m)` result mathematically covers the plus-one branch, and his
same-residue weakening also covers the minus-one one-parity cases
`(A,B)=(m,0)` and `(0,m)` when `p>m`. McTague additionally records the concrete
`m=3, p=2, N=6` valuation-2 example.

The audit did **not** locate a prior theorem giving the full mixed-parity minus-one
classification or the general `p=m-1` classification formalised here. The repository
therefore describes the minus-one result as **appearing to extend known results** and
does not make an unconditional "first" or priority claim.

No prior proof-assistant formalisation of this arithmetic-progression restricted
binomial-gcd valuation family was located, although Mathlib already formalises Kummer's
theorem and classical full-row binomial gcds, and other binomial-gcd problems have been
formalised in Lean.

See [`notes/literature.md`](notes/literature.md) for the concise boundary and
[`notes/novelty-audit-2026-09.md`](notes/novelty-audit-2026-09.md) for the full
source-level comparison and bibliography.

## Palomar packaging

The repository contains a Palomar package for the principal theorem
`PascalMinusOne.minus_one_valuation`. The Mathlib-only `Challenge.lean`
restates the restricted gcd, parity digit sums, expected valuation, and theorem
inside `PascalMinusOnePalomar`; `Solution.lean` connects those declarations
to the existing proof. `comparator.json` compares the theorem and every
project-specific definition in its type.

The predictive workflow is pinned to PalomarSubmission
`a59f25bd8a66bf6faf3a4f4260d412989c0185ea`, runs preparation before the full mechanical verifier, and
leaves `execution_profile` blank so the pinned Palomar workflow resolves its checked-in default execution profile. A green predictive
run is packaging evidence only; it is not a Palomar submission, editorial
review, acceptance, registration, or publication.

See `notes/palomar-packaging-2026-09.md` for the immutable contract pins and
scope.

## License

This repository is licensed under the Apache License 2.0. See `LICENSE`.
