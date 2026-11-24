import Mathlib.Data.Fintype.Option
import RhombicFamily.Admissibility

/-!
# Counting the designs (Sections M1.1 and M1.3)
-/

namespace RhombicFamily

/-- There are 108 cross-linking patterns. -/
theorem card_patterns : (Finset.univ.filter IsPattern).card = 108 := by decide +kernel

/-- By number of diagonals, from none to four: 1, 12, 42, 44, and 9
cross-linking patterns. -/
theorem card_patterns_of_size : ∀ k : Fin 5,
    (Finset.univ.filter fun p => IsPattern p ∧ p.card = k.val).card = ![1, 12, 42, 44, 9] k := by
  decide +kernel

/-- There are `108 × 64 = 6,912` designs. -/
theorem card_design : Fintype.card Design = 6912 := by
  rw [Fintype.card_congr designEquiv, Fintype.card_prod, Fintype.card_subtype,
    Fintype.card_finset, Fintype.card_fin, card_patterns]
  rfl

/-- The empty pattern and the nine complete patterns, indexed without repetition. -/
def emptyOrCompletePattern : Option (Fin 9) ↪ {p : Finset ShortDiagonal // IsPattern p} where
  toFun := fun
    | none => ⟨∅, by decide⟩
    | some i => ⟨completePattern i, completePattern_isPattern i⟩
  inj' := by decide +kernel

/-- The `10 × 64` designs whose cross-linking pattern is empty or complete. -/
def emptyOrCompleteDesigns : Finset Design :=
  Finset.univ.map
    ((emptyOrCompletePattern.prodMap (Function.Embedding.refl (Finset Node))).trans
      designEquiv.symm.toEmbedding)

/-- A design whose pattern is empty or complete belongs to `emptyOrCompleteDesigns`. -/
theorem mem_emptyOrCompleteDesigns (d : Design)
    (h : d.pattern = ∅ ∨ IsCompletePattern d.pattern) : d ∈ emptyOrCompleteDesigns := by
  obtain ⟨p, r, hp⟩ := d
  rw [emptyOrCompleteDesigns, Finset.mem_map]
  rcases h with h | h
  · subst h
    exact ⟨(none, r), Finset.mem_univ _, rfl⟩
  · obtain ⟨i, rfl⟩ := (isCompletePattern_iff _).mp h
    exact ⟨(some i, r), Finset.mem_univ _, rfl⟩

/-- Designs satisfying (E) may be counted within `emptyOrCompleteDesigns`. -/
theorem filter_uniform_designs (q : Design → Prop) [DecidablePred q]
    (hq : ∀ d, q d → UniformLocalEnvironment d) :
    Finset.univ.filter q = emptyOrCompleteDesigns.filter q := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨mem_emptyOrCompleteDesigns d
    (pattern_empty_or_complete_of_uniform d (hq d h)), h⟩, fun h => h.2⟩

/-- Condition (E) holds for 80 designs. -/
theorem card_uniform : (Finset.univ.filter UniformLocalEnvironment).card = 80 := by
  rw [filter_uniform_designs UniformLocalEnvironment (fun _ h => h)]
  decide +kernel

/-- Conditions (E) and (D) hold together for 31 designs. -/
theorem card_admissible : (Finset.univ.filter Admissible).card = 31 := by
  rw [filter_uniform_designs Admissible (fun _ h => h.1)]
  decide +kernel

end RhombicFamily
