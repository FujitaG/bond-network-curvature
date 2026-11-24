import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import RhombicFamily.Cell

/-!
# The 48 symmetries of the cube (Section M1.4)

Each symmetry is a signed permutation of the three coordinate axes.
-/

namespace RhombicFamily

/-- A symmetry of the cube: a permutation of the axes and a set of reversed
coordinates, the latter encoded as a site. -/
abbrev Symmetry := Fin 6 × Site

/-- The six permutations of the three axes, in lexicographic order. -/
def axisPermutation : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

/-- The action of the six axis permutations on the sites. -/
private def permutedSite : Fin 6 → Site → Site :=
  ![![0,1,2,3,4,5,6,7], ![0,1,4,5,2,3,6,7], ![0,2,1,3,4,6,5,7],
    ![0,2,4,6,1,3,5,7], ![0,4,1,5,2,6,3,7], ![0,4,2,6,1,5,3,7]]

/-- The action on sites; `coordinate_siteAction` describes it in coordinates. -/
def siteAction (s : Symmetry) (v : Site) : Site :=
  Fin.ofNat 8 (Nat.xor (permutedSite s.1 v).val s.2.val)

/-- The action on sites in coordinates: the symmetry `s = (i, r)` moves
coordinate `a` to the axis `axisPermutation i a` and reverses the coordinates
in which `r` is `+1`. -/
theorem coordinate_siteAction : ∀ (s : Symmetry) (v : Site) (a : Fin 3),
    coordinate (siteAction s v) (axisPermutation s.1 a) =
      Bool.xor (coordinate v a) (coordinate s.2 (axisPermutation s.1 a)) := by
  decide +kernel

/-- The action on nodes: permute the axis, then reverse the sign if that
coordinate is reversed. -/
def nodeAction (s : Symmetry) (c : Node) : Node :=
  let axis := axisPermutation s.1 ⟨c.val / 2, by omega⟩
  Fin.ofNat 6 (2 * axis.val +
    (Bool.xor (c.val % 2 == 1) (coordinate s.2 axis)).toNat)

/-- For sites `u < v` joined by a short diagonal, the index of that diagonal;
`0` for every other pair. -/
private def diagonalIndex (u v : Site) : ShortDiagonal :=
  match u.val, v.val with
  | 0, 1 => 0 | 0, 2 => 1 | 0, 4 => 2 | 1, 3 => 3
  | 1, 5 => 4 | 2, 3 => 5 | 2, 6 => 6 | 3, 7 => 7
  | 4, 5 => 8 | 4, 6 => 9 | 5, 7 => 10 | 6, 7 => 11
  | _, _ => 0

/-- The action on short diagonals, through their ends. -/
def diagonalAction (s : Symmetry) (e : ShortDiagonal) : ShortDiagonal :=
  let u := siteAction s (endpoints e).1
  let v := siteAction s (endpoints e).2
  if u ≤ v then diagonalIndex u v else diagonalIndex v u

/-- Every permutation of the three axes is one of the six listed. -/
theorem axisPermutation_complete : ∀ p : Fin 3 → Fin 3,
    Function.Bijective p → ∃ i : Fin 6, axisPermutation i = p := by
  decide +kernel

/-- Symmetries preserve bonding between sites and nodes. -/
theorem incident_action : ∀ (s : Symmetry) (v : Site) (c : Node),
    incident (siteAction s v) (nodeAction s c) ↔ incident v c := by
  decide +kernel

/-- The ends of the image of a short diagonal are the images of its ends. -/
theorem endpoints_action : ∀ (s : Symmetry) (e : ShortDiagonal),
    let u := siteAction s (endpoints e).1
    let v := siteAction s (endpoints e).2
    endpoints (diagonalAction s e) = (min u v, max u v) := by
  decide +kernel

/-- Distinct symmetries act differently on the sites. -/
theorem siteAction_injective : Function.Injective siteAction := by decide +kernel

/-- The composite symmetry: apply `t` first and then `s`. -/
def composeSymmetry (s t : Symmetry) : Symmetry :=
  let p := fun a => axisPermutation s.1 (axisPermutation t.1 a)
  (Fin.ofNat 6 (2 * (p 0).val + if p 1 < p 2 then 0 else 1), siteAction s t.2)

/-- The inverse symmetry. -/
def inverseSymmetry (s : Symmetry) : Symmetry :=
  let inverseAxis : Fin 6 := ![0, 1, 2, 4, 3, 5] s.1
  (inverseAxis, siteAction (inverseAxis, 0) s.2)

/-- `diagonalAction` respects composition of symmetries. -/
theorem diagonalAction_compose : ∀ s t e,
    diagonalAction (composeSymmetry s t) e = diagonalAction s (diagonalAction t e) := by
  decide +kernel

/-- `nodeAction` respects composition of symmetries. -/
theorem nodeAction_compose : ∀ s t c,
    nodeAction (composeSymmetry s t) c = nodeAction s (nodeAction t c) := by
  decide +kernel

/-- `inverseSymmetry s` inverts `diagonalAction s`. -/
theorem diagonalAction_inverse : ∀ s e,
    diagonalAction (inverseSymmetry s) (diagonalAction s e) = e := by
  decide +kernel

/-- `inverseSymmetry s` inverts `nodeAction s`. -/
theorem nodeAction_inverse : ∀ s c,
    nodeAction (inverseSymmetry s) (nodeAction s c) = c := by
  decide +kernel

/-- The image of a diagonal has `v` as an end exactly when the diagonal has
the inverse image of `v` as an end. -/
theorem hasEndpoint_diagonalAction : ∀ (s : Symmetry) (e : ShortDiagonal) (v : Site),
    hasEndpoint (diagonalAction s e) v ↔ hasEndpoint e (siteAction (inverseSymmetry s) v) := by
  decide +kernel

/-- The image of a cross-linking pattern under a symmetry is a cross-linking
pattern. -/
theorem IsPattern.image_diagonalAction {p : Finset ShortDiagonal} (h : IsPattern p)
    (s : Symmetry) : IsPattern (p.image (diagonalAction s)) := by
  intro v
  rw [Finset.filter_image]
  refine Finset.card_image_le.trans ?_
  simp only [hasEndpoint_diagonalAction]
  exact h _

end RhombicFamily
