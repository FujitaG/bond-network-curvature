import RhombicFamily.Admissibility

/-!
# The seven classes (Proposition M1.1)

The seven representatives follow Table S3 of Supplementary Methods M1: the
parent, parallel, skew, parallel with one deleted node, parallel with both
nodes on the cross-link axis deleted, parallel with both nodes on a
perpendicular axis deleted, and skew with both nodes on the axis free of
cross-links deleted.
-/

namespace RhombicFamily

/-- The parallel pattern of Table S3: the four short diagonals along `z`. -/
def parallelPattern : Finset ShortDiagonal := completePattern 8

/-- The skew pattern of Table S3: two diagonals along `x` in the face `z = -1`
and two along `y` in the face `z = +1`. -/
def skewPattern : Finset ShortDiagonal := completePattern 1

/-- The seven designs of Table S3, in the order `1, 2a, 2b, 3, 4a, 4b, 4c`.
The deleted nodes are `5` (`+z`), `4, 5` (`±z`), and `0, 1` (`±x`). -/
def representative : Fin 7 → Design :=
  ![parent, ⟨parallelPattern, ∅, completePattern_isPattern 8⟩,
    ⟨skewPattern, ∅, completePattern_isPattern 1⟩,
    ⟨parallelPattern, {5}, completePattern_isPattern 8⟩,
    ⟨parallelPattern, {4, 5}, completePattern_isPattern 8⟩,
    ⟨parallelPattern, {0, 1}, completePattern_isPattern 8⟩,
    ⟨skewPattern, {4, 5}, completePattern_isPattern 1⟩]

/-- The seven designs of Table S3 are admissible. -/
theorem representative_admissible : ∀ i, Admissible (representative i) := by
  decide +kernel

/-- The seven designs of Table S3 are pairwise inequivalent. -/
theorem representatives_inequivalent : ∀ i j,
    Equivalent (representative i) (representative j) → i = j := by
  decide +kernel

/-- For each of the nine complete patterns and every deletion set, an
admissible design is equivalent to one of the seven designs of Table S3. -/
private theorem completePatterns_covered : ∀ (i : Fin 9) (r : Finset Node),
    Admissible ⟨completePattern i, r, completePattern_isPattern i⟩ →
      ∃ j : Fin 7,
        Equivalent ⟨completePattern i, r, completePattern_isPattern i⟩ (representative j) := by
  decide +kernel

/-- Proposition M1.1: every admissible design is equivalent to a unique one of
the seven designs of Table S3. -/
theorem unique_representative (d : Design) (h : Admissible d) :
    ∃! i : Fin 7, Equivalent d (representative i) := by
  refine existsUnique_of_exists_of_unique ?_ fun i j hi hj =>
    representatives_inequivalent i j (hi.symm.trans hj)
  rcases admissible_cases d h with rfl | ⟨i, r, rfl⟩
  · exact ⟨0, by decide +kernel⟩
  · exact completePatterns_covered i r h

end RhombicFamily
