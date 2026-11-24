import Mathlib.Combinatorics.SimpleGraph.Finite
import RhombicFamily.Design

/-!
# The skeleton of a design (Definition 1)

Cross-linked sites remain separate vertices.
-/

namespace RhombicFamily

/-- A vertex of the parent cell: a site or a node. -/
abbrev CellVertex := Site ⊕ Node

/-- Sites always survive; a node survives when it is not deleted. -/
def Survives (r : Finset Node) : CellVertex → Prop
  | .inl _ => True
  | .inr c => c ∉ r

instance (r : Finset Node) (v : CellVertex) : Decidable (Survives r v) := by
  cases v <;> simp only [Survives] <;> infer_instance

/-- The vertices of the skeleton of a design. -/
abbrev SkeletonVertex (d : Design) := {v : CellVertex // Survives d.deleted v}

/-- Adjacency in the parent cell with the cross-links of `d`: two cross-linked
sites, or a site and a node bonded to it. -/
def skeletonAdj (d : Design) : CellVertex → CellVertex → Prop
  | .inl u, .inl v => u ≠ v ∧ ∃ e ∈ d.pattern, hasEndpoint e u ∧ hasEndpoint e v
  | .inl v, .inr c => incident v c
  | .inr c, .inl v => incident v c
  | .inr _, .inr _ => False

/-- The skeleton `G(Π, R)`: surviving bonds and cross-links. -/
def skeletonGraph (d : Design) : SimpleGraph (SkeletonVertex d) where
  Adj u v := skeletonAdj d u.val v.val
  symm := by
    rintro ⟨u, _⟩ ⟨v, _⟩ h
    cases u <;> cases v <;> simp only [skeletonAdj] at h ⊢
    · obtain ⟨hne, e, he, heu, hev⟩ := h
      exact ⟨Ne.symm hne, e, he, hev, heu⟩
    all_goals exact h
  loopless := by
    rintro ⟨v, _⟩
    cases v <;> simp [skeletonAdj]

instance (d : Design) : DecidableRel (skeletonGraph d).Adj := by
  rintro ⟨u, _⟩ ⟨v, _⟩
  cases u <;> cases v <;> dsimp [skeletonGraph, skeletonAdj] <;> infer_instance

/-- Condition (D): every vertex of the skeleton has degree at least three. -/
def HasMinimumDegreeThree (d : Design) : Prop :=
  ∀ v : SkeletonVertex d, 3 ≤ (skeletonGraph d).degree v

instance (d : Design) : Decidable (HasMinimumDegreeThree d) := by
  unfold HasMinimumDegreeThree; infer_instance

end RhombicFamily
