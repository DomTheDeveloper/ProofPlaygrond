# A263135 documentation reproduction

This workflow checks the exact current upstream PR #4571 head
`7f1bd9fd95a3718bb7e849620a9c96176aa0defc`.

The upstream Lean compilation passed, but `FormalConjectures:docs` failed. This
reproduction runs the same Lean and documentation stages and always uploads the
complete combined log so the failure can be diagnosed without guessing.
