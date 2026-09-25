# Final novelty and priority audit — 25 September 2026

Audit cutoff: **25 September 2026**.

This document supersedes the shorter September 2026 audit while preserving its central
conclusion. It is a source-level audit of mathematical novelty and formalisation novelty.
It is not a proof-correctness audit: the theorem layer is independently Lean-complete.
It is also not a claim of historical priority. A negative literature search can support
careful wording such as "no equivalent result was located"; it cannot prove that no
earlier unpublished, unindexed, inaccessible, differently phrased, or subsequently
discovered result exists.

## Executive conclusion

The final pre-paper audit located **no mathematically equivalent prior theorem for the
full \(p\equiv-1\pmod m\) valuation classification** proved as
**PascalMinusOne.minus_one_valuation**.

The search did, however, confirm substantial and precisely delimited prior coverage:

- McTague's Theorem Q gives the \(p\equiv1\pmod m\) valuation theorem for exactly the
  same restricted gcd family, after a direct change of notation.
- The **corrected arXiv v5** first remark on page 2 weakens McTague's congruence
  hypothesis and covers the one-parity minus-one branches
  \((A,B)=(m,0)\) and \((0,m)\) **when \(p>m\)**.
- The same corrected remark does not cover the mixed \((A,B)=(1,1)\) branch, because
  both residue classes \(+1\) and \(-1\) occur, and it does not cover any
  \(p=m-1\) case because v5 explicitly requires \(p>q\).
- McTague records the isolated example \(m=3,p=2,N=6\) with valuation \(2\), so the
  existence of a valuation-2 exception was already known. No general theorem for the
  \(p=m-1\) regime was located.
- Wu (arXiv:2606.20940v2) studies exactly the same gcd object under \(N=mn\), but the
  main product theorem assumes a prime-power modulus and requires every relevant
  non-modulus prime to be congruent to \(1\pmod m\); it therefore does not imply the
  minus-one theorem.
- Guo--Qiu--Cao--Feng--Gao (arXiv:2606.22997) gives a complete Lean formalisation of a
  **different** binomial-gcd family, so this project must not claim to be the first
  formalisation of binomial-gcd mathematics in general.

Accordingly, the paper-safe contribution statement is narrower and more specific than a
generic "new theorem" claim:

> We prove a complete \(p\)-adic valuation formula for the restricted Pascal-row gcd
> \(G(N;m)\) at primes \(p\equiv-1\pmod m\). A source-level literature audit through
> 25 September 2026 located no equivalent prior theorem for the full minus-one
> classification, and in particular no general treatment of the mixed-parity
> \((A,B)=(1,1)\) branch or of the \(p=m-1\) regime. This is a literature-search
> statement, not a claim of historical priority. McTague's Theorem Q gives the
> \(p\equiv1\pmod m\) case, and the corrected v5 same-residue remark also yields the
> one-parity minus-one branches when \(p>m\).

The existing public claim was therefore **substantively correct but slightly
underspecified**. It should be retained with the corrected-v5 boundary made explicit.

## 1. Exact theorem under review

The mathematical object is

\[
G(N;m)=\gcd\left\{\binom Nk:0<k<N,\;m\mid k\right\}.
\]

The exact Lean theorem is **PascalMinusOne.minus_one_valuation** in
PascalMinusOne/MinusOne.lean:

    theorem minus_one_valuation
        {m N p : ℕ}
        (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
        (hp : p.Prime) (hpm : p % m = m - 1) :
        padicValNat p (G N m) =
          minusOneExpectedValuation m p
            (evenDigitSum p N) (oddDigitSum p N)

The expected valuation is defined by

    if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
    else if A = 1 ∧ B = 1 ∧ m < p then 1
    else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
    else 0

where \(A\) and \(B\) are respectively the even- and odd-position base-\(p\) digit
sums of \(N\).

The hypotheses matter for the literature comparison:

- \(m\ge3\);
- \(m\mid N\);
- \(m<N\);
- \(p\) prime;
- Lean's executable congruence hypothesis \(p\bmod m=m-1\).

Under these hypotheses the proof derives the dichotomy \(p=m-1\) or \(m<p\). In
particular, the one-parity branches \((m,0)\) and \((0,m)\) are part of the theorem
also when \(p=m-1\); that low-prime portion is **not** supplied by McTague's corrected
same-residue remark.

For context, the public theorem layer also contains:

- **PascalMinusOne.plus_one_valuation**;
- **PascalMinusOne.scaling_valuation**;
- **PascalMinusOne.modulus_three_valuation**;
- **PascalMinusOne.modulus_four_valuation**;
- **PascalMinusOne.modulus_six_valuation**.

Those results are compared separately below rather than being bundled into one novelty
claim.

## 2. Audit method

The earlier notes were treated as a hypothesis to be stress-tested, not as an
authority. The search proceeded in four directions.

### 2.1 Exact-object and notation searches

Searches included combinations and variants of:

- gcd of binomial coefficients in arithmetic progressions;
- gcd of \(C(n,q),C(n,2q),\ldots\);
- \(G(N;m)\), \(g(m,n)\), restricted Pascal-row gcd;
- common divisors of \(C(N,mj)\);
- binomial coefficients with lower index divisible by \(m\);
- \(p\)-adic valuation of restricted binomial gcds;
- Kummer carries plus restricted gcd;
- digit sums plus binomial gcd;
- \(p\equiv-1\pmod m\), \(p+1\equiv0\pmod m\), and \(p=m-1\);
- alternating, parity-separated, even-position, and odd-position base-\(p\) digit
  sums;
- same-residue powers modulo the step size;
- arithmetic-progression subsets of Pascal rows.

Equivalent formulations were checked even when they did not use the project's
notation.

### 2.2 Citation-chain searches

The audit followed references backward and forward from McTague, Wu, Hong,
Joris--Oestreicher--Steinig, Kaplan--Levy, and later restricted-binomial-gcd papers.
This exposed earlier full-row, odd-index, coprimality-restricted, truncated-row, and
fixed-gcd-class results, but no theorem equivalent to the full minus-one
classification.

### 2.3 Version-sensitive primary-source checking

Primary papers/preprints were opened wherever reasonably available. Exact theorem,
remark, definition, or formal statement locations were checked rather than relying on
titles or snippets.

A particularly important version check is McTague:

- arXiv v4, 26 September 2016, page 2, first remark says the condition can be weakened
  to \(p\) and \(q\) relatively prime plus a same-residue condition;
- arXiv v5, 25 July 2018, page 2, first remark corrects this to
  **\(p>q\) being relatively prime** plus the same-residue condition;
- the arXiv record for v5 explicitly says "typos corrected in first remark on p.2".

The v5 correction is mathematically material here. The audit therefore uses v5, not
the broader-looking v4 wording, when assessing the \(p=m-1\) boundary.

### 2.4 Formalisation searches

Searches covered Lean, Coq/Rocq, Isabelle/HOL and public code repositories using the
paper title, McTague's name/arXiv number, the \(C(n,qk)\) notation, "binomial gcd",
and restricted-gcd variants.

The search found:

- Mathlib infrastructure for binomial coefficients, gcd, digits, and Kummer-style
  valuation results;
- the Guo--Qiu--Cao--Feng--Gao 2026 Lean formalisation of a different binomial-gcd
  object;
- September 2026 Lean-math-lab research notes for Erdős problem 699 that **cite
  McTague's Theorem Q as an external theorem**, but no Lean implementation of Theorem Q
  was located there.

No machine-checked formalisation of McTague's arithmetic-progression restricted family,
or of the minus-one theorem proved here, was located.

## 3. McTague: exact comparison

Primary source:

Carl McTague, *On the Greatest Common Divisor of Binomial Coefficients
C(n,q), C(n,2q), C(n,3q), ...*, American Mathematical Monthly 124(4) (2017),
353--356, DOI 10.4169/amer.math.monthly.124.4.353; latest corrected preprint
arXiv:1510.06696v5, 25 July 2018.

### 3.1 Same object

McTague's Theorem Q studies

\[
\gcd_{0<k<n/q}\binom n{qk},
\]

which is exactly \(G(N;m)\) after \(n=N\) and \(q=m\) when \(m\mid N\).

### 3.2 Plus-one theorem

Theorem Q, page 1, states that for \(n>q>0\) and prime
\(p\equiv1\pmod q\),

\[
v_p\!\left(\gcd_{0<k<n/q}\binom n{qk}\right)
=
\begin{cases}
1,&\alpha_p(n)\le q,\\
0,&\text{otherwise},
\end{cases}
\]

where \(\alpha_p(n)\) is the base-\(p\) digit sum.

Under the project's hypotheses \(m\mid N\) and \(p\equiv1\pmod m\),
\(\alpha_p(N)\equiv N\equiv0\pmod m\). Since \(N>0\), the positive digit sum obeys

\[
\alpha_p(N)\le m \quad\Longleftrightarrow\quad \alpha_p(N)=m.
\]

Thus **PascalMinusOne.plus_one_valuation** is mathematically equivalent to
McTague's theorem in the project's divisibility regime, with a straightforward
translation of notation. The plus-one theorem is old mathematics and should be
presented as a formalised supporting theorem, not as a new mathematical result.

### 3.3 Corrected same-residue weakening

The first remark on page 2 of **v5** says that \(p\equiv1\pmod q\) may be weakened,
for example, to:

- \(p>q\);
- \(p\) and \(q\) relatively prime; and
- all powers \(p^{i_1},\ldots,p^{i_r}\) in a minimal power-sum expansion of \(n\)
  having the same residue modulo \(q\).

For \(p\equiv-1\pmod m\),

\[
p^i\equiv(-1)^i\pmod m.
\]

The minimal power-sum expansion repeats \(p^i\) exactly \(d_i\) times, where \(d_i\)
is the \(i\)-th base-\(p\) digit. Therefore:

- \((A,B)=(m,0)\) means all \(m\) terms occur at even exponents and all have residue
  \(+1\pmod m\);
- \((A,B)=(0,m)\) means all \(m\) terms occur at odd exponents and all have residue
  \(-1\pmod m\).

When \(p>m\), the corrected v5 hypotheses are met and the digit-sum condition is
\(\alpha_p(N)=m\). Hence McTague gives valuation \(1\) in exactly these two
one-parity \(p>m\) arms.

This is not merely a resemblance: it is a direct specialization of the corrected
remark.

### 3.4 What the same-residue weakening does not cover

It does not cover \((A,B)=(1,1)\), because the minimal expansion contains one term
with residue \(+1\) and one with residue \(-1\) modulo \(m\). Since \(m\ge3\), those
two residues are distinct.

It also does not cover **any \(p=m-1\) case**, because corrected v5 requires
\(p>q=m\).

This second point is the main sharpening produced by the final audit. The previous
public wording said that McTague covered "part of the minus-one \(p>m\) regime",
which is true, but the theorem-level comparison should explicitly record that the
one-parity \(p=m-1\) arms also lie outside corrected v5.

### 3.5 The valuation-2 example

The same page-2 remark gives

\[
v_2\!\left(\gcd_{0<k<2}\binom6{3k}\right)=v_2(20)=2.
\]

This is exactly the project's \(m=3,p=2=m-1,N=6\), \((A,B)=(1,1)\) instance.

Consequently:

- "valuation 2 can occur" is not new;
- the isolated \(m=3,p=2,N=6\) example is not new;
- no source was located that upgrades this example to the project's general
  \(p=m-1,(A,B)=(1,1)\) theorem;
- no source was located that gives the project's one-parity \(p=m-1\) arms either.

### 3.6 Older McTague result for step 2

Theorem 2 in the 2017 note cites Lemma 12 of McTague's 2014
*The Cayley plane and string bordism* for the step-\(2\) odd-prime case. This is an
important predecessor but does not supply the general \(m\ge3\) minus-one theorem.

## 4. Wu 2026: exact comparison

Primary source:

Chai Wah Wu, *Computing the Greatest Common Divisor of Binomial Coefficients
C(mn,mk)*, arXiv:2606.20940v2, revised 4 August 2026.

Wu defines on page 1

\[
g(m,n)=\gcd\left\{\binom{mn}{mk}:1\le k<n\right\}.
\]

Thus \(g(m,n)=G(mn;m)\): this is exactly the same gcd object with \(N=mn\).

Wu also restates McTague's \(p\equiv1\pmod m\) valuation formula on pages 1--2.

### 4.1 Wu Theorem 1 and scaling

Wu's Theorem 1, page 2, assumes \(m=p^t\) is a prime power at the valuation prime and
states that \(v_p(g(m,n))\) is \(1\) when \(n\) is a power of \(p\), and \(0\)
otherwise. Its proof explicitly observes that multiplying both summands by \(p^t\)
shifts their base-\(p\) expansions without changing the number of carries.

That is the same elementary Kummer carry-shift mechanism behind
**PascalMinusOne.scaling_valuation**. The repository's scaling theorem is packaged in
a reusable exact equality for arbitrary \(c,q,N'\), but the underlying mathematical
mechanism is standard and independently visible in Wu. It should not be promoted as a
headline novelty claim.

### 4.2 Wu Theorem 2

Wu's Theorem 2, page 2, assumes:

- \(m=p^t\) is a prime power; and
- every prime factor \(q\) of \(\binom{mn}{m}\) is either \(p\) or satisfies
  \(q\equiv1\pmod m\).

It then gives an explicit squarefree product formula for \(g(m,n)\).

For \(m\ge3\), a non-modulus prime with \(q\equiv-1\pmod m\) is excluded by this
hypothesis rather than classified. Therefore Theorem 2 cannot be specialized to the
general minus-one theorem. Its displayed \(m=3\) and \(m=4\) examples are examples
under the theorem's restrictive hypothesis, not complete all-prime formulas for those
moduli.

No theorem in v2 was located that gives the mixed-parity branch or the general
\(p=m-1\) regime.

## 5. Guo--Qiu--Cao--Feng--Gao 2026: exact comparison

Primary source:

Dakai Guo, Ruichen Qiu, Yichuan Cao, Ruyong Feng, Xiao-Shan Gao,
*A Greatest Common Divisor Criterion of Certain Binomial Coefficients*,
arXiv:2606.22997, June 2026.

Their paper defines

\[
D(k)=\gcd_{2\le q\le k+1}\binom{qk}{k},\qquad n=k+1.
\]

This is structurally different from \(G(N;m)\):

- the lower index is fixed at \(k\);
- the upper row varies through \(qk\).

The paper proves a criterion for \(D(k)=1\) in terms of the largest exact prime-power
component of \(k+1\).

### 5.1 Formalisation boundary

Section 3 explicitly gives the Lean benchmark predicate

    def GCDCondition (k : Nat) : Prop :=
      (Finset.range k).gcd
        (fun i => Nat.choose ((i + 2) * k) k) = 1

and the theorem

    theorem gcdCondition_iff_primePowerCondition
      (k : Nat) (hk : 2 <= k) :
      GCDCondition k <-> PrimePowerCondition (k + 1)

together with a paper-level \(D(k)\) definition.

This is genuine prior Lean formalisation of a binomial-gcd theorem. It is not a
formalisation of McTague's arithmetic-progression subset of a fixed Pascal row and is
not equivalent to any of the project's principal valuation theorems.

The correct formalisation claim is therefore narrow:

> No prior proof-assistant formalisation of this arithmetic-progression restricted
> Pascal-row gcd valuation family, or of the full minus-one classification, was located
> in the audit.

The repository must not say "first formalisation of binomial gcds".

## 6. Other inspected literature and why it does not subsume the theorem

### Joris--Oestreicher--Steinig 1985

H. Joris, C. Oestreicher and J. Steinig,
*The greatest common divisor of certain sets of binomial coefficients*,
Journal of Number Theory 21(1) (1985), 101--119,
DOI 10.1016/0022-314X(85)90013-7.

The published abstract states that the paper determines the gcd of any number of
**consecutive terms in a fixed row** of Pascal's triangle. McTague also describes it
on page 2 as the different generalization involving
\(\binom nr,\binom n{r+1},\ldots,\binom ns\).
This is a different selector from the arithmetic progression \(m\mid k\).

### Kaplan--Levy 2004

Gil Kaplan and Dan Levy, *GCD of Truncated Rows in Pascal's Triangle*,
Integers 4 (2004), A14.

The paper studies
\(\gcd(\binom nt,\binom n{t+1},\ldots,\binom nn)\) and gives its prime
factorisation. Again the selector is a consecutive/truncated block, not multiples of a
fixed step.

### Hong 2016

Siao Hong, *The greatest common divisor of certain binomial coefficients*,
Comptes Rendus Mathématique 354(8) (2016), 756--761,
DOI 10.1016/j.crma.2016.06.001.

Hong's main identity concerns

\[
\gcd\left\{\binom{mn}{k}:1\le k\le mn,\ \gcd(k,m)=1\right\}.
\]

The restriction is coprimality of the lower index with \(m\), essentially the
complementary kind of selector to \(m\mid k\). It does not determine \(G(N;m)\).

### Xiao--Yuan--Lin 2022

Jiaqi Xiao, Pingzhi Yuan and Xucan Lin,
*The Greatest Common Divisor of Certain Set of Binomial Coefficients*,
Mathematical Theory and Applications 42(1) (2022), 85--91.

Their main displayed gcd runs over a central consecutive interval
\(a<k<n-a\). This belongs to the truncated-row/Hong problem line, not the
arithmetic-progression family.

### Chiu--Yuan--Zhou 2023

Sunben Chiu, Pingzhi Yuan and Tao Zhou,
*On the Greatest Common Divisor of Binomial Coefficients*,
Bulletin of the Korean Mathematical Society 60(4) (2023), 863--872,
DOI 10.4134/BKMS.b220166.

This paper studies \(p\)-adic valuations of gcds over a central interval with an
additional condition \((n,k)>1\). It does not specialize to \(m\mid k\).

### Chung--Yang--Zhou 2025

Chan-Liang Chung, Tse-Chung Yang and Kanglun Zhou,
*The Greatest Common Divisor of Sets of Binomial Coefficients with Restrictions*,
Contemporary Mathematics 6(1) (2025), 971--985,
DOI 10.37256/cm.6120255017.

They define classes such as

\[
A_d(n)=\left\{\binom nk:1\le k\le n-1,\ \gcd(n,k)=d\right\}
\]

and obtain partial results for \(d=2\). The paper itself restates McTague's Theorem Q
as the result for a lower index required to be a multiple of a positive integer.
Its own fixed-gcd-class results do not give the project's full progression gcd.

### Classical antecedents

Ram's 1909 full-row gcd theorem, Mendelsohn's odd-index result, Albree's
coprimality-restricted result, and Kummer's carry theorem are important ancestors and
proof tools. None was found to encode the project's parity-separated minus-one
classification.

## 7. Theorem-level comparison matrix

The categories below describe the relationship to prior work; they are not novelty
scores.

| Project component | Strongest evidence-supported relationship to prior work | Exact boundary / source |
| --- | --- | --- |
| Full **PascalMinusOne.minus_one_valuation** | **No equivalent result located in the audited literature**; strict subfamilies are known | McTague v5 covers the one-parity arms only for \(p>m\); no source located for the full piecewise theorem |
| Mixed \((A,B)=(1,1),\,p>m\) | **No equivalent result located** | McTague v5 page 2 requires all powers in the minimal expansion to have the same residue; the mixed branch contains both \(+1\) and \(-1\) |
| Mixed \((A,B)=(1,1),\,p=m-1\) | **Prior work covers only a strict special case** | McTague v5 page 2 records \(m=3,p=2,N=6\), valuation 2; no general theorem located |
| One-parity \((m,0)/(0,m),\,p>m\) | **Follows directly from known prior work** | McTague v5 page 2 same-residue weakening with \(q=m\) |
| One-parity \((m,0)/(0,m),\,p=m-1\) | **No equivalent result located** | McTague v5 requires \(p>q=m\); the broader-looking v4 text was corrected in v5 |
| **PascalMinusOne.plus_one_valuation** | **Equivalent after straightforward translation** | McTague Theorem Q, page 1; \(m\mid N\) converts \(\alpha_p(N)\le m\) to \(\alpha_p(N)=m\) |
| **PascalMinusOne.scaling_valuation** | **Standard/repackaged Kummer carry-shift mechanism** | Wu Theorem 1, page 2, explicitly uses invariance of carries under multiplication by a \(p\)-power; do not promote as independent novelty |
| Complete \(m=3\) formula | **No identical complete all-prime formula located; follows readily as an application of the theorem layer** | Combines scaling, plus-one, and minus-one cases; McTague gives only portions and one \(p=2,N=6\) example |
| Complete \(m=4\) formula | **No identical complete all-prime formula located; follows readily as an application** | Wu has conditional \(m=4\) examples, not a complete all-prime formula |
| Complete \(m=6\) formula | **No identical complete all-prime formula located; follows readily as an application** | No equivalent complete formula located |
| Proof-assistant formalisation of this family | **No equivalent formalisation located** | Guo et al. formalise a different gcd family; public searches found no Lean/Coq/Rocq/Isabelle/HOL formalisation of McTague's family |

## 8. Answers to the audit questions

1. **Is the full \(p\equiv-1\pmod m\) theorem already present?**  
   No equivalent theorem was located. McTague supplies strict subfamilies, not the full
   classification.

2. **Is the mixed \((1,1)\) case known in general?**  
   No general equivalent result was located. McTague's same-residue hypothesis
   specifically excludes it.

3. **Is the \(p>m\) valuation-1 versus \(p=m-1\) valuation-2 mixed distinction known
   in general?**  
   No. The audit found McTague's isolated valuation-2 example but no theorem giving
   the general dichotomy.

4. **Is the \(p=m-1\) classification known beyond isolated examples?**  
   No general source was located. This includes both the mixed valuation-2 arm and the
   one-parity valuation-1 arms.

5. **Are the one-parity cases covered by McTague?**  
   Yes **when \(p>m\)**, by a direct application of the corrected v5 same-residue
   remark. No, not when \(p=m-1\), because v5 requires \(p>q\).

6. **Is the plus-one theorem old mathematics?**  
   Yes. Under \(m\mid N\), it is McTague's Theorem Q after a straightforward
   translation.

7. **Does the scaling theorem have independent mathematical novelty?**  
   The exact reusable Lean theorem is useful formal infrastructure, but the carry-shift
   argument is elementary and appears explicitly in Wu's Theorem 1 proof. It should not
   be advertised as a mathematical novelty contribution.

8. **Are the \(m=3,4,6\) formulas independently new?**  
   No identical complete formulas were located, but they are straightforward
   applications/corollaries assembled from the general theorem layer. They should be
   presented as applications, not as separate headline novelty claims.

9. **Was this restricted family previously formalised?**  
   No prior formalisation of McTague's arithmetic-progression fixed-row family was
   located in Lean, Coq/Rocq, Isabelle or HOL.

10. **Is the formalisation plausibly new?**  
    The defensible statement is "no prior equivalent formalisation was located."
    Guo et al. show that binomial-gcd theorems have already been formalised in Lean.

11. **Is current repository wording too strong?**  
    No substantive overclaim was found. The main correction is precision: state
    explicitly that corrected McTague v5 covers one-parity minus-one cases only for
    \(p>m\), and that the \(p=m-1\) one-parity cases also remain outside that prior
    theorem.

12. **Is the current wording too cautious?**  
    Only slightly. It can responsibly be sharpened from "part of the minus-one
    \(p>m\) regime" to the exact statement that McTague covers the two one-parity
    \(p>m\) arms, while no equivalent source was located for the mixed branch or the
    \(p=m-1\) regime. It should not be strengthened to "first", "new", or an
    unconditional priority claim.

## 9. Mathematical novelty, formalisation novelty, and verification status

These are separate claims.

### Mathematical novelty

The evidence supports an **apparent extension** claim for the full minus-one theorem.
The portions for which no equivalent source was located are, most notably:

- the mixed \((1,1),p>m\) branch;
- the general mixed \((1,1),p=m-1\) valuation-2 branch;
- the one-parity \(p=m-1\) cases;
- their assembly into one complete minus-one valuation classification.

This is a negative-search conclusion, not proof of priority.

### Formalisation novelty

No prior proof-assistant formalisation of this restricted fixed-row
arithmetic-progression family was located. That statement is plausible and
source-supported as a search report, but it should remain phrased negatively.

### Packaging and verification

Lean completeness and Palomar registration establish formal verification/provenance
facts for the stated artifact. They do **not** establish that the mathematics is new
and should never be cited as evidence of historical priority.

## 10. Paper-safe novelty wording

### Suggested abstract wording

> For primes \(p\equiv-1\pmod m\) we prove a complete \(p\)-adic valuation
> classification for the restricted Pascal-row gcd \(G(N;m)\). We are not aware of an
> equivalent prior result: a source-level literature audit through 25 September 2026
> found McTague's corrected same-residue extension to cover the one-parity \(p>m\)
> subcases, but not the mixed-parity branch or the \(p=m-1\) regime.

### Suggested introduction wording

> McTague's Theorem Q determines the \(p\)-adic valuation for
> \(p\equiv1\pmod m\), and the corrected first remark in arXiv:1510.06696v5
> extends that argument to a same-residue condition which, for
> \(p\equiv-1\pmod m\), yields the one-parity cases when \(p>m\). The same-residue
> condition excludes the mixed \((1,1)\) case, while the corrected remark's
> \(p>m\) hypothesis excludes the \(p=m-1\) regime. Our audit through
> 25 September 2026 located no equivalent prior theorem covering those remaining cases
> or assembling the full minus-one classification.

A footnote or literature paragraph should add that McTague already records the
\(m=3,p=2,N=6\) valuation-2 example.

## 11. Claims that should not be made

The paper and repository should avoid:

- "the first theorem" or "the first proof" without qualification;
- "the first formalisation of a binomial-gcd theorem";
- "McTague does not cover the minus-one case" as a blanket statement;
- "the \(p=m-1\) valuation-2 phenomenon was previously unknown";
- "the scaling theorem is new";
- presenting the \(m=3,4,6\) corollaries as independent headline novelties;
- treating Lean completeness, Palomar registration, or a clean mechanised proof as
  evidence of mathematical priority;
- relying on McTague v4's broader-looking wording instead of the corrected v5 remark.

## 12. Negative-search limitations and unresolved uncertainty

The audit was broad but cannot be exhaustive in the logical sense. In particular:

- inaccessible subscription material may contain relevant remarks not indexed by
  searchable metadata;
- theses, proceedings, lecture notes, non-English sources, or private manuscripts may
  be poorly indexed;
- a broader theorem may exist in notation so different that the search terms did not
  expose it;
- citation databases and ordinary web search can omit references;
- proof-assistant code may exist in private repositories or in public repositories
  without searchable mathematical terminology.

No specific unresolved source currently appears likely to overturn the contribution
boundary. The remaining uncertainty is the ordinary uncertainty of negative historical
search, not a known mathematical mismatch.

## 13. Literature-audit conclusion for the paper stage

From a literature-audit perspective the project is ready to move to paper preparation.

The supported posture is:

- **known prior mathematics:** McTague plus-one theorem; McTague one-parity
  minus-one arms for \(p>m\); isolated valuation-2 example; standard Kummer
  carry-shift/scaling mechanism;
- **project contribution for which no equivalent source was located:** the full
  minus-one classification, specifically the mixed branch and the complete
  \(p=m-1\) regime;
- **applications rather than separate novelty claims:** complete \(m=3,4,6\)
  formulas;
- **formalisation statement:** no equivalent proof-assistant formalisation located,
  while acknowledging Guo et al.'s different Lean binomial-gcd formalisation;
- **priority posture:** apparent extension / no-equivalent-source-located, not
  "first" or unconditional priority.

## Bibliography

- Carl McTague, *On the Greatest Common Divisor of Binomial Coefficients
  C(n,q), C(n,2q), C(n,3q), ...*, American Mathematical Monthly 124(4)
  (2017), 353--356. DOI: 10.4169/amer.math.monthly.124.4.353.
  Corrected preprint: arXiv:1510.06696v5, 25 July 2018.
  https://arxiv.org/abs/1510.06696
- Carl McTague, *The Cayley plane and string bordism*, Geometry & Topology 18(4)
  (2014), 2045--2078. DOI: 10.2140/gt.2014.18.2045.
- Chai Wah Wu, *Computing the Greatest Common Divisor of Binomial Coefficients
  C(mn,mk)*, arXiv:2606.20940v2, 4 August 2026.
  https://arxiv.org/abs/2606.20940
- Dakai Guo, Ruichen Qiu, Yichuan Cao, Ruyong Feng, Xiao-Shan Gao,
  *A Greatest Common Divisor Criterion of Certain Binomial Coefficients*,
  arXiv:2606.22997, June 2026.
  https://arxiv.org/abs/2606.22997
- Siao Hong, *The greatest common divisor of certain binomial coefficients*,
  Comptes Rendus Mathématique 354(8) (2016), 756--761.
  DOI: 10.1016/j.crma.2016.06.001.
- H. Joris, C. Oestreicher, J. Steinig, *The greatest common divisor of certain sets
  of binomial coefficients*, Journal of Number Theory 21(1) (1985), 101--119.
  DOI: 10.1016/0022-314X(85)90013-7.
- Gil Kaplan, Dan Levy, *GCD of Truncated Rows in Pascal's Triangle*,
  Integers 4 (2004), A14.
- Jiaqi Xiao, Pingzhi Yuan, Xucan Lin, *The Greatest Common Divisor of Certain Set
  of Binomial Coefficients*, Mathematical Theory and Applications 42(1) (2022),
  85--91.
- Sunben Chiu, Pingzhi Yuan, Tao Zhou, *On the Greatest Common Divisor of Binomial
  Coefficients*, Bulletin of the Korean Mathematical Society 60(4) (2023),
  863--872. DOI: 10.4134/BKMS.b220166.
- Chan-Liang Chung, Tse-Chung Yang, Kanglun Zhou, *The Greatest Common Divisor of
  Sets of Binomial Coefficients with Restrictions*, Contemporary Mathematics 6(1)
  (2025), 971--985. DOI: 10.37256/cm.6120255017.
- B. Ram, *Common factors of n!/[m!(n-m)!], (m=1,2,...,n-1)*,
  Journal of the Indian Mathematical Club (Madras) 1 (1909), 39--43.
- E. E. Kummer, *Über die Ergänzungssätze zu den allgemeinen
  Reciprocitätsgesetzen*, Journal für die reine und angewandte Mathematik 44
  (1852), 93--146.
- Andrew Granville, *Arithmetic properties of binomial coefficients I: Binomial
  coefficients modulo prime powers*, CMS Conference Proceedings 20 (1997),
  253--276.
