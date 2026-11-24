# Bond-network curvature: supplementary code

| Directory | Contents |
|---|---|
| [`lean/`](lean/) | Lean 4 proofs of the lemmas, propositions, and theorems of the Supplementary Theory (Sections T1 and T2) and of Supplementary Methods M1 |
| [`enumeration/`](enumeration/) | A Python script that enumerates the 6,912 designs of Supplementary Methods M1 and checks its counts and Table S3 apart from the point-group symbols |

The enumeration needs only the Python standard library:

```sh
python3 enumeration/enumerate_family.py
```

Building the Lean proofs is described in [`lean/README.md`](lean/README.md).

The discrete Ricci curvature and the effective curvature of any graph can be
computed in the web application
[Curvature Studio](https://studio.curvature.workers.dev)
([source](https://github.com/FujitaG/curvature-studio)).

## Licence

Copyright 2026 Daishi Fujita. Released under the Apache License 2.0; see
[LICENSE](LICENSE).
