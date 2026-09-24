# Pascal Minus-One GCD

Lean/Mathlib formalisation of the restricted binomial gcd

\[
G(N;m)=\gcd\left\{\binom Nk:0<k<N,\ m\mid k\right\}.
\]

The repository now formalises the \`p ≡ -1 (mod m)\` valuation theorem, the complementary
\`p ≡ 1 (mod m)\` branch needed by the project, the trailing-zero scaling reduction, and
complete prime-by-prime valuation formulas for \`m = 3, 4, 6\`.

## Formalised results

### Minus-one branch

Assume \`m ≥ 3\`, \`m ∣ N\`, \`m < N\`, \`p\` prime, and
\`p % m = m - 1\`. Write the base-\`p\` expansion of \`N\` as
\`N = Σ d_i p^i\`, and set

- \`A = Σ_{i even} d_i\`,
- \`B = Σ_{i odd} d_i\`.

Then the valuation is

- \`2\` for \`(A,B)=(1,1)\` and \`p=m-1\`;
- \`1\` for \`(A,B)=(1,1)\` and \`p>m\`;
- \`1\` for \`(A,B)=(m,0)\` or \`(0,m)\`;
- \`0\` otherwise.

The Lean theorem is \`PascalMinusOne.minus_one_valuation\`.

### Plus-one branch

Assume \`0 < m\`, \`m ∣ N\`, \`m < N\`, \`p\` prime, and
\`p % m = 1 % m\`. Then

\[
v_p(G(N;m))=
\begin{cases}
1,&\text{if the base-}p\text{ digit sum of }N\text{ is }m,\\
0,&\text{otherwise.}
\end{cases}
\]

The formulation deliberately includes \`m = 1\` and \`m = 2\`, because those reduced
moduli occur after scaling in the small-modulus corollaries. The Lean theorem is
\`PascalMinusOne.plus_one_valuation\`.

### Scaling

For prime \`p\` and natural numbers \`c,q,N'\`,

\[
v_p\!\left(G(p^cN';p^cq)\right)=v_p\!\left(G(N';q)\right).
\]

This is \`PascalMinusOne.scaling_valuation\`.

### Complete formulas for \`m = 3,4,6\`

The public theorem layer contains

- \`PascalMinusOne.modulus_three_valuation\`,
- \`PascalMinusOne.modulus_four_valuation\`,
- \`PascalMinusOne.modulus_six_valuation\`.

Each theorem covers **every prime**. The cases are dispatched as follows:

| modulus | primes dividing the modulus | remaining primes |
| --- | --- | --- |
| \`3\` | \`p=3\`: scale to modulus \`1\`, then use the plus-one theorem | residues \`1\` or \`-1\` mod \`3\` |
| \`4\` | \`p=2\`: scale to modulus \`1\`, then use the plus-one theorem | residues \`1\` or \`-1\` mod \`4\` |
| \`6\` | \`p=2\`: scale to modulus \`3\`; \`p=3\`: scale to modulus \`2\` | residues \`1\` or \`-1\` mod \`6\` |

The corresponding piecewise right-hand sides are exposed as
\`modulusThreeExpectedValuation\`, \`modulusFourExpectedValuation\`, and
\`modulusSixExpectedValuation\`.

## Verification status

The advertised theorem layer is Lean-complete on the current proof branch. All of the
results above are proved without theorem placeholders. The project Lean sources contain
no \`sorry\`, \`admit\`, or replacement \`axiom\` declarations.

CI checks \`lake build\`, the Python regression suite, the independent finite reference
sweep, and an explicit zero-\`sorry\` gate. The computational checks are regression
evidence only; they are not used as substitutes for the infinite Lean proofs.

## Layout

- \`PascalMinusOne/Basic.lean\`: admissible indices, \`G\`, and gcd valuation infrastructure.
- \`PascalMinusOne/Digits.lean\`: base-\`p\` digit and parity-sum infrastructure.
- \`PascalMinusOne/Kummer.lean\`: Mathlib Kummer wrapper and zero-borrow/digitwise bridge.
- \`PascalMinusOne/SignedTokens.lean\`: reusable \`±1\` zero-sum layer.
- \`PascalMinusOne/MinusOne.lean\`: minus-one branch lemmas and \`minus_one_valuation\`.
- \`PascalMinusOne/PlusOne.lean\`: plus-one branch and \`plus_one_valuation\`.
- \`PascalMinusOne/Scaling.lean\`: trailing-zero scaling theorem.
- \`PascalMinusOne/SmallModuli.lean\`: complete \`m=3,4,6\` prime-by-prime corollaries.
- \`scripts/reference_check.py\`: independent finite regression checker.
- \`tests/test_reference_checker.py\`: Python regression tests.
- \`notes/\`: proof architecture, literature boundary, and discovery provenance.

## Build and test

The project pins Mathlib to commit
\`bd6c1abe5f55b6c3856172d6a23703e0888f5286\` and Lean \`v4.35.0-rc2\`.

\`\`\`bash
lake update
lake build
python3 -m unittest discover -s tests -v
python3 scripts/reference_check.py
\`\`\`

## Mathlib foundation

The central imported result is \`padicValNat_choose\` from
\`Mathlib.NumberTheory.Padics.PadicVal.Basic\`, Mathlib's Kummer theorem for the
\`p\`-adic valuation of binomial coefficients. The formalisation also uses Mathlib's
base-\`p\` digit and digit-sum lemmas.

## Literature and novelty

See \`notes/literature.md\`. The plus-one direction has known prior art and is formalised
here as part of the complete theorem layer. Lean completeness does **not** establish
novelty of the minus-one result. This repository makes no publication-level novelty
claim without a separate source-level literature audit.

## License

No license has been selected yet. Add one deliberately before public distribution.
