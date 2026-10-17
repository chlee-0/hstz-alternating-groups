# Unmodified OpenAI tensor-square sources

The 36 Lean files under `OAI/RepresentationTheory/Saxl/` are byte-identical
copies from [openai/math](https://github.com/openai/math), commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, from its `lean/` directory.
This includes the transitive OpenAI imports needed by HSTZ, not the full
upstream repository. Original module paths and declaration namespaces are kept.

No imports, comments, definitions or proofs in these files are changed.
HSTZ-specific extensions and API adaptations belong in `HSTZ/`, outside this
directory. The upstream used Lean 4.34.1; this repository's own pinned toolchain
is specified at its root and its compatibility must be verified by building.

The source is licensed under Apache-2.0; the upstream license is retained in
[LICENSE](LICENSE). No claim is made that this subset contains the complete
upstream tensor-square theorems.
