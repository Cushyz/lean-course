import Dihedral.Computable

open Nat CoxeterSystem DihedralGroup List

example : s_α α0 = s0 := by
  simp

-- `s0` is the edge from `1` with degree `(1, 0)`.
example : (1 : D∞) —[α0]→ (cs.simple 0) := by
  dsimp [IsEdge]
  rw [one_mul]
  rw [s_alpha_alpha0]
  rfl

example : CurveNeighborhood 1 {a := 2, b := 2} = { s0s1_pow 2, s1s0_pow 2 } := by
  rw [curve_nbhd_one_diag {a := 2, b := 2} rfl]

/-- Certified balanced identity instance, beyond the smallest displayed example. -/
example : CurveNeighborhood 1 {a := 3, b := 3} = { s0s1_pow 3, s1s0_pow 3 } := by
  rw [curve_nbhd_one_diag {a := 3, b := 3} rfl]

/-- Certified unbalanced identity instance. -/
example : CurveNeighborhood 1 {a := 2, b := 3} = { s_alpha_d {a := 2, b := 3} } := by
  rw [curve_nbhd_one_offdiag]
  norm_num

lemma curveNeighborhood_s0_23 :
    CurveNeighborhood s0 {a := 2, b := 3} = {s0 * s_alpha_d {a := 2, b := 3}} := by
  rw [main_theorem s0 {a := 2, b := 3}]
  have h_ends : ends_in_s0 s0 := by
    rw [s0]
    change ends_in_s0 (sr (0 : ℤ))
    exact (ends_in_s0_sr (0 : ℤ)).mpr (by norm_num)
  have h_max := max_ad_ends_s0 s0 {a := 2, b := 3} h_ends
  rw [if_neg (by norm_num), if_pos (by norm_num)] at h_max
  obtain ⟨m, -, h_uniq_eq⟩ := exists_unique_max_ad_ne_one s0 {a := 2, b := 3} (by decide)
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw_is_max, rfl⟩
    rw [h_uniq_eq w hw_is_max, h_uniq_eq _ h_max]
  · rintro rfl
    exact ⟨s_alpha_d {a := 2, b := 3}, h_max, rfl⟩

example {u v : Vertex} {d : Degree} :
    v ∈ CurveNeighborhood_computable u d ↔ v ∈ CurveNeighborhood u d :=
  mem_CurveNeighborhood_computable_iff

example {u : Vertex} {d : Degree} :
    (CurveNeighborhood_computable u d : Set Vertex) = CurveNeighborhood u d :=
  coe_CurveNeighborhood_computable u d

example : s0s1_pow 2 ∈ CurveNeighborhood_computable 1 ⟨2, 2⟩ := by
  rw [mem_CurveNeighborhood_computable_iff]
  rw [curve_nbhd_one_diag {a := 2, b := 2} rfl]
  simp

/-- Certified translated rotation-base computation. -/
example : CurveNeighborhood_computable s0 ⟨2, 3⟩ = {r (3 : ℤ)} := by
  native_decide

/-- Certified translated reflection-base computation. -/
example : CurveNeighborhood_computable s1 ⟨3, 3⟩ = {sr (4 : ℤ)} := by
  native_decide

/-- The search space used by the computable model has the advertised linear bound. -/
example (u : Vertex) (d : Degree) :
    (Ad_finset u d).card ≤ 2 * (d.a + d.b + 2) :=
  card_Ad_finset_le u d

example : s0 * s_alpha_d {a := 2, b := 3} ∈
    CurveNeighborhood_computable s0 ⟨2, 3⟩ := by
  rw [mem_CurveNeighborhood_computable_iff]
  rw [curveNeighborhood_s0_23]
  simp

-- Small executable sanity checks for the computable API.
#eval CurveNeighborhood_computable 1 ⟨2, 2⟩
#eval CurveNeighborhood_computable s0 ⟨2, 3⟩
#eval CurveNeighborhood_computable s1 ⟨3, 3⟩

