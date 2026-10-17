# Formalization of the Heide–Saxl–Tiep–Zalesski Conjecture on Tensor Squares of Alternating Groups in Lean 4

This repository contains a Lean 4 formalization, using Mathlib, of **universal tensor
squares for the alternating groups** $A_n$, $n \ge 5$: an irreducible representation whose
tensor square contains every irreducible representation. Their existence was conjectured by
Heide, Saxl, Tiep and Zalesski. The Lean formalization was carried out primarily by AI
models, Claude Opus 5.5 and GPT-6.1 Sol.

## Scope

**Prior work used here.** OpenAI's *Universal Tensor Squares for Symmetric Groups* and
*A Cyclic Polytabloid Proof of Saxl's Conjecture* prove tensor-square covering results for
the symmetric groups $S_n$, and come with a Lean development of Specht modules. The
TauCeti library provides Specht modules, the Murnaghan–Nakayama rule and the
representation theory of finite groups in Lean.

**Results established here.** For every $n \ge 5$, the alternating group $A_n$ has an
irreducible representation whose tensor square contains every irreducible representation.
For $n \ge 16$ the witness is the restriction of an explicit non-self-conjugate Specht
module, built on OpenAI's Specht-module development; for $5 \le n \le 15$ the result is
proved with finite character certificates checked against TauCeti's Specht characters.
**To our knowledge, this statement has not been proved elsewhere**: Heide, Saxl, Tiep and
Zalesski state it as a conjecture, and OpenAI's preprints treat the symmetric groups and
mention the alternating-group conjecture only as related work.

**Scope of the formalization.** The statement is proved for every $n \ge 5$ without
additional hypotheses, using only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Main result

For every $n \ge 5$, there is an irreducible complex representation $V$ of $A_n$ such that
every irreducible complex representation of $A_n$ occurs in $V \otimes V$.

## Where to start

Start with [Statements.lean](Statements.lean): `HSTZ.tensor_square_covering_ge5` states the
result in full, using only Mathlib's notions. The same proposition is defined in
[TensorSquareCovering.lean](HSTZ/TensorSquareCovering.lean), which imports only Mathlib.
The proof is split into
[LargeDegreeStatements.lean](HSTZ/LargeDegreeStatements.lean) ($n \ge 16$),
[TauCetiFinite.lean](HSTZ/TauCetiFinite.lean) ($5 \le n \le 15$) and
[TauCetiIntegration.lean](HSTZ/TauCetiIntegration.lean), which combines the two ranges.

To build, use Lean 4.35.0 and run `lake exe cache get` (optional) and `lake build`; Lake
fetches Mathlib and TauCeti at the versions pinned in `lake-manifest.json`.

## Attribution

**Heide, Saxl, Tiep and Zalesski (2013).** *Conjugacy action, induced representations and
the Steinberg square for simple groups of Lie type*. Proceedings of the London Mathematical
Society 106(4), 908–930. The conjecture is Remark 1.3(3).
[doi:10.1112/plms/pds062](https://doi.org/10.1112/plms/pds062) ·
[arXiv:1209.1768](https://arxiv.org/abs/1209.1768).

**OpenAI (2026).** *Universal Tensor Squares for Symmetric Groups* and *A Cyclic
Polytabloid Proof of Saxl's Conjecture*. OpenAI Math Release preprints, with Lean sources
([commit adc7f1241](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a)).
The 36 Lean files used here are included unmodified in
[OpenAITensorSquares](OpenAITensorSquares/README.md) under their Apache-2.0 license.

**[TauCeti](https://github.com/TauCetiProject/TauCeti)** and
**[Mathlib](https://github.com/leanprover-community/mathlib4)** (Apache-2.0) are Lake
dependencies and are not included here.

## License

Apache License 2.0; see [LICENSE](LICENSE).
