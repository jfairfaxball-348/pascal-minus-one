# Palomar packaging audit — 25 September 2026

This note records the immutable external contract used to prepare the repository
for predictive Palomar mechanical pre-flight. It does **not** record a Palomar
submission or registration.

## Contract pins

- PalomarSubmission: `a59f25bd8a66bf6faf3a4f4260d412989c0185ea`
- PalomarPolicy: `792c7c0b9e798bd02719e795ef11fa2b5929e067`
- PalomarTemplate: `cb5c79b69a740d2dc299071fc35994627050d77a`
- Lean toolchain: `leanprover/lean4:v4.35.0-rc2`
- Mathlib: `bd6c1abe5f55b6c3856172d6a23703e0888f5286`
- formalization.yaml schema: `v0.4`
- predictive execution profile: `palomar-standard-v1`\n- predictive caller mode: single `mode: full` reusable-workflow call, matching the pinned PalomarSubmission README example

A preparation-only predictive attempt reached Palomar but returned the Palomar-owned diagnostic `palomar.reporting_failed` (`retryable: true`, `repairable: false`, `next_action: No repository change is indicated`). The final caller therefore follows the pinned PalomarSubmission README's documented single `mode: full` predictive pattern; full mode repeats the same intake preparation before continuing to the expensive verifier.\n\nThe submission protocol was also checked against
`https://submit.palomar-registry.org/llms.txt` on 25 September 2026. The
reusable workflow reference and `pipeline_commit` are pinned to the same full
PalomarSubmission SHA. The predictive workflow runs preparation first and only
then the full mechanical verifier.

## Selected entry

The package advertises one principal theorem:

- `PascalMinusOnePalomar.minus_one_valuation`

Comparator additionally checks the five definitions needed to state it:

- `PascalMinusOnePalomar.G`
- `PascalMinusOnePalomar.parityDigitSums`
- `PascalMinusOnePalomar.evenDigitSum`
- `PascalMinusOnePalomar.oddDigitSum`
- `PascalMinusOnePalomar.minusOneExpectedValuation`

The Challenge imports only Mathlib. The Solution imports the substantive project
and discharges the advertised theorem from
`PascalMinusOne.minus_one_valuation`.

## Provenance and novelty wording

Palomar's `original-proof` source type is used to record that this repository is
the originating mathematical source for the submitted theorem, rather than a
formalisation of an external proof. It is not used as an unconditional priority
claim.

The public novelty wording remains:

> «A source-level literature audit through September 2026 located no equivalent prior theorem for the full "p ≡ -1 (mod m)" valuation formula. McTague's 2017 theorem and its same-residue weakening cover the "p ≡ 1 (mod m)" branch and part of the minus-one "p>m" regime, but not the mixed-parity branch or the general "p=m-1" classification proved here.»

## Licence

The package uses Apache-2.0, matching the convention used by the maintainer's
other Palomar-packaged research repositories and the Palomar template.
