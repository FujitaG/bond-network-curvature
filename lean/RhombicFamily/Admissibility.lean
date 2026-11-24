import Mathlib.Tactic.DeriveFintype
import RhombicFamily.Skeleton

/-!
# Ligand molecules, local environments, and admissibility (Definitions 2 and 3)
-/

namespace RhombicFamily

/-- A candidate ligand molecule: a single site or a cross-linked pair. -/
inductive Ligand where
  | single (site : Site)
  | pair (diagonal : ShortDiagonal)
  deriving DecidableEq, Fintype

/-- The ligand molecules of a design: the diagonals of its pattern and the
sites that the pattern does not cover. -/
def IsLigand (d : Design) : Ligand → Prop
  | .single v => ∀ e ∈ d.pattern, ¬ hasEndpoint e v
  | .pair e => e ∈ d.pattern

instance (d : Design) (l : Ligand) : Decidable (IsLigand d l) := by
  cases l <;> unfold IsLigand <;> infer_instance

/-- The set of ligand molecules of a design. -/
def ligands (d : Design) : Finset Ligand :=
  Finset.univ.filter (IsLigand d)

/-- Membership in `ligands d` is `IsLigand d`. -/
@[simp] theorem mem_ligands (d : Design) (l : Ligand) :
    l ∈ ligands d ↔ IsLigand d l := by simp [ligands]

/-- A local environment (Definition 2): `single k` for a single site with `k`
deleted neighbours, `pair a b` for a pair with `a` deleted shared neighbours
and `b` deleted exclusive neighbours. -/
inductive LocalEnvironment where
  | single (deleted : ℕ)
  | pair (shared exclusive : ℕ)
  deriving DecidableEq

/-- The local environment of a ligand molecule in a design. -/
def localEnvironment (d : Design) : Ligand → LocalEnvironment
  | .single v => .single (d.deleted.filter (incident v)).card
  | .pair e =>
    let u := (endpoints e).1
    let v := (endpoints e).2
    .pair (d.deleted.filter (fun c => incident u c ∧ incident v c)).card
      (d.deleted.filter (fun c => Xor' (incident u c) (incident v c))).card

/-- Condition (E): all ligand molecules have the same local environment. -/
def UniformLocalEnvironment (d : Design) : Prop :=
  ∀ l ∈ ligands d, ∀ m ∈ ligands d, localEnvironment d l = localEnvironment d m

instance (d : Design) : Decidable (UniformLocalEnvironment d) := by
  unfold UniformLocalEnvironment; infer_instance

/-- An admissible design (Definition 3): a design satisfying conditions (E)
and (D). -/
def Admissible (d : Design) : Prop :=
  UniformLocalEnvironment d ∧ HasMinimumDegreeThree d

instance (d : Design) : Decidable (Admissible d) := by
  unfold Admissible; infer_instance

/-- Cross-linking is all or none: under (E) the pattern is empty or complete,
because a single site and a pair have different local environments. -/
theorem pattern_empty_or_complete_of_uniform (d : Design) (hu : UniformLocalEnvironment d) :
    d.pattern = ∅ ∨ IsCompletePattern d.pattern := by
  rcases d.pattern.eq_empty_or_nonempty with hp | ⟨e, he⟩
  · exact Or.inl hp
  refine Or.inr (isCompletePattern_of_covered d.isPattern fun v => ?_)
  by_contra hv
  have hs : Ligand.single v ∈ ligands d := by simpa [IsLigand] using hv
  have h := hu _ hs (.pair e) ((mem_ligands d (.pair e)).2 he)
  simp [localEnvironment] at h

/-- With the empty cross-linking pattern, condition (D) forces the deletion set
to be empty. -/
theorem deleted_eq_empty_of_empty_pattern : ∀ r : Finset Node,
    HasMinimumDegreeThree ⟨∅, r, by decide⟩ → r = ∅ := by
  decide +kernel

/-- An admissible design is the parent or has one of the nine complete
patterns. -/
theorem admissible_cases (d : Design) (h : Admissible d) :
    d = parent ∨ ∃ (i : Fin 9) (r : Finset Node),
      d = ⟨completePattern i, r, completePattern_isPattern i⟩ := by
  obtain ⟨p, r, hpat⟩ := d
  rcases pattern_empty_or_complete_of_uniform ⟨p, r, hpat⟩ h.1 with rfl | hp
  · obtain rfl := deleted_eq_empty_of_empty_pattern r h.2
    exact Or.inl rfl
  · obtain ⟨i, rfl⟩ := (isCompletePattern_iff p).mp hp
    exact Or.inr ⟨i, r, rfl⟩

end RhombicFamily
