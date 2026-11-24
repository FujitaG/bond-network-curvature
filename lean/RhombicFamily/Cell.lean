import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation

/-!
# The parent cell (Section M1.1)

The sites, the nodes, and their bonds form the graph of the rhombic
dodecahedron, with 14 vertices and 24 edges; the short diagonals are those of
its rhombic faces.
-/

namespace RhombicFamily

/-- The eight ligand sites, the vertices of the cube. -/
abbrev Site := Fin 8
/-- The six metal nodes `±x`, `±y`, `±z`. -/
abbrev Node := Fin 6
/-- The twelve short diagonals, the edges of the cube. -/
abbrev ShortDiagonal := Fin 12

/-- The coordinate of a site along an axis (`false` for `-1`, `true` for `+1`):
the coordinates of site `v` are the binary digits of `v`, with `x` least
significant. -/
def coordinate (v : Site) (axis : Fin 3) : Bool := v.val.testBit axis.val

/-- A site is bonded to the node `2a + b` when its coordinate `a` equals `b`:
nodes `0, 1` are `-x, +x`, nodes `2, 3` are `-y, +y`, and nodes `4, 5` are
`-z, +z`. -/
def incident (v : Site) (c : Node) : Prop :=
  coordinate v ⟨c.val / 2, by omega⟩ = (c.val % 2 == 1)

instance (v : Site) (c : Node) : Decidable (incident v c) := by
  unfold incident; infer_instance

/-- The two ends of each short diagonal, in increasing order. -/
def endpoints : ShortDiagonal → Site × Site :=
  ![(0,1), (0,2), (0,4), (1,3), (1,5), (2,3),
    (2,6), (3,7), (4,5), (4,6), (5,7), (6,7)]

/-- The twelve short diagonals are the pairs of distinct sites with two common
nodes (Section M1.1). -/
theorem shortDiagonals_iff_common_nodes : ∀ u v : Site,
    ((∃ e : ShortDiagonal, endpoints e = (min u v, max u v)) ↔
      (Finset.univ.filter (fun c => incident u c ∧ incident v c)).card = 2) := by
  decide +kernel

/-- The site `v` is an end of the short diagonal `e`. -/
def hasEndpoint (e : ShortDiagonal) (v : Site) : Prop :=
  (endpoints e).1 = v ∨ (endpoints e).2 = v

instance (e : ShortDiagonal) (v : Site) : Decidable (hasEndpoint e v) := by
  unfold hasEndpoint; infer_instance

/-- A cross-linking pattern: no site occurs in two of its diagonals. The
pattern need not cover every site. -/
def IsPattern (p : Finset ShortDiagonal) : Prop :=
  ∀ v : Site, (p.filter (fun e => hasEndpoint e v)).card ≤ 1

instance (p : Finset ShortDiagonal) : Decidable (IsPattern p) := by
  unfold IsPattern; infer_instance

/-- A complete pattern: every site occurs in exactly one of its diagonals. -/
def IsCompletePattern (p : Finset ShortDiagonal) : Prop :=
  ∀ v : Site, (p.filter (fun e => hasEndpoint e v)).card = 1

instance (p : Finset ShortDiagonal) : Decidable (IsCompletePattern p) := by
  unfold IsCompletePattern; infer_instance

/-- A pattern covering every site is complete. -/
theorem isCompletePattern_of_covered {p : Finset ShortDiagonal} (hp : IsPattern p)
    (hc : ∀ v : Site, ∃ e ∈ p, hasEndpoint e v) : IsCompletePattern p := fun v =>
  let ⟨e, he, hv⟩ := hc v
  (hp v).antisymm (Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hv⟩⟩)

/-- The nine complete patterns, each of four diagonals (`isCompletePattern_iff`). -/
def completePattern : Fin 9 → Finset ShortDiagonal :=
  ![{0,5,8,11}, {0,5,9,10}, {0,6,7,8}, {1,3,8,11}, {1,3,9,10},
    {1,4,7,9}, {2,3,6,10}, {2,4,5,11}, {2,4,6,7}]

/-- A set of short diagonals is a complete pattern if and only if it is one of
the nine patterns listed in `completePattern`. -/
theorem isCompletePattern_iff : ∀ p : Finset ShortDiagonal,
    IsCompletePattern p ↔ ∃ i : Fin 9, completePattern i = p := by
  decide +kernel

/-- The nine complete patterns are cross-linking patterns. -/
theorem completePattern_isPattern (i : Fin 9) : IsPattern (completePattern i) :=
  fun v => ((isCompletePattern_iff _).mpr ⟨i, rfl⟩ v).le

end RhombicFamily
