import RhombicFamily.Symmetry

/-!
# Designs (Definition 1) and their equivalence
-/

namespace RhombicFamily

/-- A design `(Π, R)` (Definition 1): a cross-linking pattern and a set of
deleted nodes. -/
structure Design where
  /-- The cross-linking pattern `Π`. -/
  pattern : Finset ShortDiagonal
  /-- The deletion set `R`. -/
  deleted : Finset Node
  /-- No site occurs in two diagonals of `Π`. -/
  isPattern : IsPattern pattern

instance : DecidableEq Design := fun d e =>
  decidable_of_iff (d.pattern = e.pattern ∧ d.deleted = e.deleted)
    (by cases d; cases e; simp only [Design.mk.injEq])

/-- Designs correspond to pairs of a cross-linking pattern and a deletion set. -/
def designEquiv : Design ≃ {p : Finset ShortDiagonal // IsPattern p} × Finset Node where
  toFun d := (⟨d.pattern, d.isPattern⟩, d.deleted)
  invFun x := ⟨x.1.1, x.2, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Design := Fintype.ofEquiv _ designEquiv.symm

/-- The parent: no cross-link and no deleted node (cage 1). -/
def parent : Design := ⟨∅, ∅, by decide⟩

/-- The image of a design under a symmetry of the cube. -/
def transform (s : Symmetry) (d : Design) : Design :=
  ⟨d.pattern.image (diagonalAction s), d.deleted.image (nodeAction s),
    d.isPattern.image_diagonalAction s⟩

/-- `transform` respects composition of symmetries. -/
theorem transform_compose (s t : Symmetry) (d : Design) :
    transform (composeSymmetry s t) d = transform s (transform t d) := by
  simp [transform, Finset.image_image, Function.comp_def,
    funext (diagonalAction_compose s t), funext (nodeAction_compose s t)]

/-- `inverseSymmetry s` inverts `transform s`. -/
theorem transform_inverse (s : Symmetry) (d : Design) :
    transform (inverseSymmetry s) (transform s d) = d := by
  simp [transform, Finset.image_image,
    Function.comp_def, diagonalAction_inverse, nodeAction_inverse]

/-- Two designs are equivalent when a symmetry of the cube maps one onto the
other. -/
def Equivalent (d e : Design) : Prop := ∃ s : Symmetry, transform s d = e

instance (d e : Design) : Decidable (Equivalent d e) := by
  unfold Equivalent; infer_instance

/-- Equivalence of designs is symmetric. -/
theorem Equivalent.symm {d e : Design} (h : Equivalent d e) : Equivalent e d := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨inverseSymmetry s, transform_inverse s d⟩

/-- Equivalence of designs is transitive. -/
theorem Equivalent.trans {d e f : Design}
    (h : Equivalent d e) (h' : Equivalent e f) : Equivalent d f := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨t, rfl⟩ := h'
  exact ⟨composeSymmetry t s, transform_compose t s d⟩

end RhombicFamily
