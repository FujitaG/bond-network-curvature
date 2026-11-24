import RhombicFamily.Admissibility
import RhombicFamily.Cell
import RhombicFamily.Classification
import RhombicFamily.Consequences
import RhombicFamily.Counts
import RhombicFamily.Design
import RhombicFamily.Skeleton
import RhombicFamily.Symmetry
import RhombicFamily.Table

/-!
# The family of seven designs (Supplementary Methods M1)

`Cell` defines the parent cell, `Symmetry` its 48 symmetries, and `Design` the
designs and their equivalence. `Skeleton` defines the skeleton graph and
condition (D); `Admissibility` defines the ligand molecules, their local
environments, condition (E), and admissibility. `Classification` defines the
seven designs of Table S3 and proves Proposition M1.1, `Consequences` proves
Lemma M1.2, `Counts` establishes the counts of cross-linking patterns and
designs, and `Table` proves the pattern geometry, environments, orders, sizes,
and skeleton counts of Table S3.
-/
