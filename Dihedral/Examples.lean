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

lemma curveNeighborhood_s0_23 :
    CurveNeighborhood s0 {a := 2, b := 3} = {s0 * s_alpha_d {a := 2, b := 3}} := by
  rw [main_theorem s0 {a := 2, b := 3}]
  have h_ends : ends_in_s0 s0 := by
    rw [s0]
    change ends_in_s0 (sr (0 : ℤ))
    exact (ends_in_s0_sr (0 : ℤ)).mpr (by norm_num)
  have h_u_ne_1 : s0 ≠ 1 := by
    decide
  have h_max := max_ad_ends_s0 s0 {a := 2, b := 3} h_ends
  rw [if_neg (by norm_num), if_pos (by norm_num)] at h_max
  have h_unique := exists_unique_max_ad_ne_one s0 {a := 2, b := 3} h_u_ne_1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw_is_max, rfl⟩
    have h_w_eq : w = s_alpha_d {a := 2, b := 3} := by
      rcases h_unique with ⟨m, hm, h_uniq_eq⟩
      have h1 : w = m := by exact h_uniq_eq w hw_is_max
      have h2 : s_alpha_d {a := 2, b := 3} = m := h_uniq_eq _ h_max
      rw [h1, h2]
    rw [h_w_eq]
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

example : s0 * s_alpha_d {a := 2, b := 3} ∈
    CurveNeighborhood_computable s0 ⟨2, 3⟩ := by
  rw [mem_CurveNeighborhood_computable_iff]
  rw [curveNeighborhood_s0_23]
  simp

-- Small executable sanity checks for the computable API.
#eval CurveNeighborhood_computable 1 ⟨2, 2⟩
#eval CurveNeighborhood_computable s0 ⟨2, 3⟩
#eval CurveNeighborhood_computable s1 ⟨3, 3⟩

