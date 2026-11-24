import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import RhombicFamily.Admissibility

/-!
# Consequences of admissibility (Lemma M1.2)
-/

namespace RhombicFamily

/-- The action of a symmetry of the cube on ligand molecules. -/
def ligandAction (s : Symmetry) : Ligand → Ligand
  | .single v => .single (siteAction s v)
  | .pair e => .pair (diagonalAction s e)

/-- The symmetries preserving the design map any ligand molecule to any other. -/
def LigandsTransitive (d : Design) : Prop :=
  ∀ l ∈ ligands d, ∀ m ∈ ligands d,
    ∃ s : Symmetry, transform s d = d ∧ ligandAction s l = m

instance (d : Design) : Decidable (LigandsTransitive d) := by
  unfold LigandsTransitive; infer_instance

/-- The vertices within `n` steps of site `0`. -/
private def reached (d : Design) : ℕ → Finset (SkeletonVertex d)
  | 0 => {⟨.inl 0, trivial⟩}
  | n + 1 => reached d n ∪ (reached d n).biUnion (fun u => (skeletonGraph d).neighborFinset u)

/-- Every vertex in `reached d n` is joined to site `0` by a walk. -/
private theorem reached_sound (d : Design) (n : ℕ) {v : SkeletonVertex d}
    (h : v ∈ reached d n) : (skeletonGraph d).Reachable ⟨.inl 0, trivial⟩ v := by
  induction n generalizing v with
  | zero =>
      obtain rfl := (Finset.mem_singleton.mp h : v = ⟨.inl 0, trivial⟩)
      exact SimpleGraph.Reachable.rfl
  | succ n ih =>
      rcases Finset.mem_union.mp h with h | h
      · exact ih h
      · obtain ⟨u, hu, huv⟩ := Finset.mem_biUnion.mp h
        exact (ih hu).trans (((skeletonGraph d).mem_neighborFinset u v).mp huv).reachable

/-- For each of the nine complete patterns and every deletion set, an
admissible design has at most two deleted nodes, every vertex of its skeleton
within four steps of site `0`, and ligand molecules that are all equivalent. -/
private theorem completePatterns_consequences : ∀ (i : Fin 9) (r : Finset Node),
    Admissible ⟨completePattern i, r, completePattern_isPattern i⟩ → r.card ≤ 2 ∧
      (∀ v : SkeletonVertex ⟨completePattern i, r, completePattern_isPattern i⟩,
        v ∈ reached ⟨completePattern i, r, completePattern_isPattern i⟩ 4) ∧
      LigandsTransitive ⟨completePattern i, r, completePattern_isPattern i⟩ := by
  decide +kernel

/-- Lemma M1.2: every admissible design has at most two deleted nodes, a
connected skeleton, and ligand molecules that are all equivalent under the
symmetries preserving the design. -/
theorem admissible_consequences (d : Design) (h : Admissible d) :
    d.deleted.card ≤ 2 ∧ (skeletonGraph d).Connected ∧ LigandsTransitive d := by
  have key : d.deleted.card ≤ 2 ∧ (∀ v : SkeletonVertex d, v ∈ reached d 4) ∧
      LigandsTransitive d := by
    rcases admissible_cases d h with rfl | ⟨i, r, rfl⟩
    · decide +kernel
    · exact completePatterns_consequences i r h
  refine ⟨key.1, ?_, key.2.2⟩
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    ⟨⟨.inl 0, trivial⟩, fun v => reached_sound d 4 (key.2.1 v)⟩

end RhombicFamily
