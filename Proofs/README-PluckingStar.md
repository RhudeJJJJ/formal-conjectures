# Complete Lean proof of star plucking unimodality

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization, source comparison, execution and submission under the author's direction, 14 October 2026.

Written proof: *Unimodality of star plucking polynomials with delays one and two*, 13 October 2026, attached with source records to [intake #7309](https://github.com/google-deepmind/formal-conjectures/issues/7309).

## Versioned target and definition

The target is Conjecture4.1 in Ibarra, Landry, Montoya-Vega and Przytycki, *Exploring unimodality of the plucking polynomial with delay function*, arXiv:2311.18059v1, 29 November2023:
https://arxiv.org/html/2311.18059v1

A star with n leaves is represented by its right-to-left order Fin n. An arbitrary delay function f:Fin n -> Nat is used in the definitions. A leaf i is eligible precisely when f(i)=1. Removing it preserves the order via Fin.succAbove and lowers each surviving delay d to max(1,d-1). The empty star has polynomial1; a nonempty star with no eligible leaf has polynomial0.

The source's isolated phrase in Definition1.7 about a zero initial condition is ambiguous. This operational recurrence agrees with its displayed recurrence, examples and Proposition2.5. Both the original statement module and the independent audit use the actual recursive polynomial, not the factorized expression as a definition. A later published chapter is not asserted to have been checked; the target is the identified versioned arXiv formulation.

PolynomialUnimodal means that there exists a natural peak index, with all coefficient comparisons weakly increasing before it and weakly decreasing after it. Plateaus and the zero polynomial are included. Coefficients are exact integers; no numerical q is chosen.

## Complete proof chain

1. Coefficient sequences on integer indices are extended by zero. Multiplication by a quantum integer is defined as a uniform finite moving sum.
2. Its adjacent difference is proved to be a(j+1)-a(j+1-h). A peak in a implies no negative difference followed by a positive difference in the new sequence.
3. Finite support and nonnegativity turn this no-reversal condition into an actual peak. This is proved explicitly rather than treated as an equivalent definition without proof.
4. Every nonnegative integer sequence supported in0,...,m has a unimodal first window of lengthm, for m>=1. Subsequent uniform factors preserve the property. This proves the nonnegative-integer weighted factorial statement.
5. The full delayed star recurrence is defined independently. Induction proves the all-one formula; a second argument proves the binary-delay factorization from that recurrence, for all n and all arrangements.
6. A separate actual Polynomial Int is defined by the same leaf-removal recurrence. polynomial_coeff proves its coefficient at every natural exponent equals the recursively computed sequence. Negative exponent values of the sequence vanish. Nonnegativity of the polynomial coefficients is also proved.
7. The all-size theorem conjecture4_1 concerns this actual recursive polynomial for every f with values1 or2, including the empty and one-leaf stars.

The source's star factorization and first-factor proposition remain attributed to its authors. The kernel proof supplies the complete general closure and application. The manuscript's version with arbitrary nonnegative real weights is not claimed to be formalized: the weighted auxiliary Lean theorem uses integer coefficients. The binary-delay conjecture itself is proved in full.

## Independent type audit and boundary control

PluckingStarAudit.lean defines the polynomial recurrence and unimodality predicate independently, proves equality of its recurrence to the proof's recurrence by induction, and writes the exact intended repository theorem. It imports no upstream placeholder statement.

The audit also proves that the known delay-four pattern21412 is not unimodal: the coefficients at exponents4,5,6 are5,4,5. This negative control is outside the binary-delay hypothesis.

Both full proof and audit compile without warnings. All twelve audited declarations depend only on propext, Classical.choice and Quot.sound. No sorryAx, custom axiom or native-evaluation trust is used. This is a universal induction/order proof, not an enumeration over star sizes.

## Reproduction

Pins: Lean4.33.1 / Mathlib0df444a360eaa60ab8c11dca51a86af692955474.

```sh
lake exe cache get
mkdir -p .lake/build/lib/lean/Proofs
lake env lean -o .lake/build/lib/lean/Proofs/PluckingStarProof.olean Proofs/PluckingStarProof.lean
lake env lean Proofs/PluckingStarAudit.lean
```

The environment used the already disclosed narrow readlink adapter: a failed /proc/<own-pid>/exe lookup falls back to /proc/self/exe. The official Lean executable, elaborator, sources and kernel are unchanged. Official archive SHA256:890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. Normal supported installations need no adapter.

SHA256:
- PluckingStarProof.lean:12a24ab7bdf82b7c1f1a6e5bec7a39727bd447216ebd168449091e6deb9443fc
- PluckingStarAudit.lean:6f8d60d1cab9fa2423988469f0591778e35ded7a55a38e536c81cbe1d099a251

The separate Python audit was rerun on all510 binary delay vectors on1–8 leaves, with the delay-four negative control. Those finite checks are regression diagnostics and are not premises of the universal Lean proof. No independent peer-review, maintainer acceptance, or worldwide priority claim follows from the author-workflow certificate.

