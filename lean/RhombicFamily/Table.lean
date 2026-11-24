import RhombicFamily.Classification

/-!
# Table S3

Table S3 gives one representative of each of the seven classes of admissible
designs under the symmetries of the cube.
-/

namespace RhombicFamily

/-- The parallel pattern consists of the four short diagonals along `z`. -/
theorem mem_parallelPattern : ∀ e : ShortDiagonal, e ∈ parallelPattern ↔
    coordinate (endpoints e).1 2 ≠ coordinate (endpoints e).2 2 := by
  decide +kernel

/-- The skew pattern consists of the two diagonals along `x` in the face
`z = -1` and the two diagonals along `y` in the face `z = +1`. -/
theorem mem_skewPattern : ∀ e : ShortDiagonal, e ∈ skewPattern ↔
    (coordinate (endpoints e).1 0 ≠ coordinate (endpoints e).2 0 ∧
      coordinate (endpoints e).1 2 = false) ∨
    (coordinate (endpoints e).1 1 ≠ coordinate (endpoints e).2 1 ∧
      coordinate (endpoints e).1 2 = true) := by
  decide +kernel

/-- Column "Environment": the design has ligand molecules, and every one of
them has the listed local environment. -/
theorem representative_environments : ∀ i : Fin 7,
    (ligands (representative i)).Nonempty ∧ ∀ l ∈ ligands (representative i),
      localEnvironment (representative i) l =
        ![.single 0, .pair 0 0, .pair 0 0, .pair 0 1, .pair 0 2, .pair 1 0, .pair 1 0] i := by
  decide +kernel

/-- Column "Order": the number of cube symmetries preserving the design. -/
theorem representative_stabilizer_orders : ∀ i : Fin 7,
    (Finset.univ.filter (fun s : Symmetry =>
      transform s (representative i) = representative i)).card = ![48, 16, 8, 8, 16, 8, 8] i := by
  decide +kernel

/-- Column "Size": the number of designs in the class, that is, the number of
distinct images of the design under the 48 symmetries. -/
theorem representative_class_sizes : ∀ i : Fin 7,
    (Finset.univ.image (fun s : Symmetry => transform s (representative i))).card =
      ![1, 3, 6, 6, 3, 6, 6] i := by
  decide +kernel

/-- Columns "Vertices" and "Edges" of the skeleton, cross-links included. -/
theorem representative_skeleton_counts : ∀ i : Fin 7,
    Fintype.card (SkeletonVertex (representative i)) = ![14, 14, 14, 13, 12, 12, 12] i ∧
    (skeletonGraph (representative i)).edgeFinset.card = ![24, 28, 28, 24, 20, 20, 20] i := by
  decide +kernel

end RhombicFamily
