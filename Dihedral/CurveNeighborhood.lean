import Dihedral.Ends

open CoxeterSystem DihedralGroup Nat

lemma edge_left_mul (g u v : Vertex) (α : Root) (h : IsEdge u v α) :
    IsEdge (g * u) (g * v) α := by
  dsimp [IsEdge] at *
  rw [h, mul_assoc]

lemma chain_left_mul (g u v : Vertex) (d : Degree) (h : HasChain u v d) :
    HasChain (g * u) (g * v) d := by
  induction h with
  | refl  =>
    exact HasChain.refl (g * u)
  | step h_prev h_edge ih =>
    exact HasChain.step ih (edge_left_mul g _ _ _ h_edge)

lemma CurveNeighborhood_max (h : v ∈ CurveNeighborhood u d) :
     ∀ w ∈ ReachableSet u d, ℓ w ≤ ℓ v := by
  rw [CurveNeighborhood] at h
  intro w hw
  by_contra h_lt
  rw [not_le, ← lt_iff_length_lt] at h_lt
  have h_le : v ≤ w := le_of_lt h_lt
  have h_eq := h.2 w hw h_le
  rw [h_eq] at h_lt
  exact (lt_self_iff_false w).mp h_lt

theorem len_mul_ad_le_curve_nbhd_max (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ Ad 1 d) (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u * z) ≤ ℓ v := by
  have h_deg_z : φ z ≤ d := by
      simp only [Ad, one_mul, length_one, zero_add, Degreele_le_def, true_and,
        Set.mem_setOf_eq] at hz
      exact hz
  have h_chain_uz : HasChain u (u * z) (getDegree z) := by
    have := chain_left_mul u 1 z _ (trivial_chain z)
    simpa only [mul_one] using this
  have h_uz_in_Re : u * z ∈ ReachableSet u d := by use getDegree z
  exact CurveNeighborhood_max hv (u * z) h_uz_in_Re

theorem deg_inv_mul_le_curve_nbhd (u : Vertex) (d : Degree) (v : Vertex)
     (hv : v ∈ CurveNeighborhood u d) :
   φ (u⁻¹ * v) ≤ d := by
  have h_v_reachable : v ∈ ReachableSet u d := by
    rw [CurveNeighborhood] at hv
    exact hv.1
  rcases h_v_reachable with ⟨dv, h_chain_v, h_dv_le_d⟩
  have h_chain_inv_u_v : HasChain (u⁻¹ * u) (u⁻¹ * v) dv := chain_left_mul u⁻¹ u v dv h_chain_v
  simp only [inv_mul_cancel] at h_chain_inv_u_v
  have h_phi_le_dv := inv_mul_degree_le_of_chain 1 (u⁻¹ * v) dv h_chain_inv_u_v
  simp only [inv_one, one_mul, Degreele_le_def] at h_phi_le_dv
  exact le_trans h_phi_le_dv h_dv_le_d

theorem inv_mul_len_le_curve_nbhd_one_max (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ CurveNeighborhood 1 d) (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u⁻¹ * v) ≤ ℓ z := by
  rw [CurveNeighborhood] at hv
  rcases hv with ⟨h_v_in_Re, -⟩
  rcases h_v_in_Re with ⟨dv, h_chain_v, h_dv_le_d⟩
  have h_chain_inv : HasChain (u⁻¹ * u) (u⁻¹ * v) dv := chain_left_mul u⁻¹ u v dv h_chain_v
  simp only [inv_mul_cancel] at h_chain_inv
  set w := u⁻¹ * v with hw
  have h_w_in_Re : w ∈ ReachableSet 1 d := by use dv
  exact CurveNeighborhood_max hz w h_w_in_Re

lemma left_descent_0_r_pos (k : ℤ)
    (h : cs.IsLeftDescent (r k) (0 : Fin 2)) : 0 < k := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 0 = s0 := rfl
  simp only [Fin.isValue, length_r] at h
  rw [hs, s0, sr_mul_r, zero_add, length_sr] at h
  split_ifs at h with hk <;> omega

lemma left_descent_0_sr_nonpos (k : ℤ)
    (h : cs.IsLeftDescent (sr k) (0 : Fin 2)) : k ≤ 0 := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 0 = s0 := rfl
  simp only [Fin.isValue, length_sr, gt_iff_lt] at h
  rw [hs, s0, sr_mul_sr, sub_zero, length_r] at h
  split_ifs at h with hk <;> omega

lemma left_descent_1_r_neg (k : ℤ)
    (h : cs.IsLeftDescent (r k) (1 : Fin 2)) : k < 0 := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 1 = s1 := rfl
  simp only [Fin.isValue, length_r] at h
  rw [hs, s1, sr_mul_r, length_sr] at h
  split_ifs at h with hk <;> omega

lemma left_descent_1_sr_pos (k : ℤ)
    (h : cs.IsLeftDescent (sr k) (1 : Fin 2)) : 0 < k := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 1 = s1 := rfl
  simp only [Fin.isValue, length_sr, gt_iff_lt] at h
  rw [hs, s1, sr_mul_sr, length_r] at h
  split_ifs at h with hk <;> omega

lemma degree_le_of_left_descent (i : Fin 2) (z : D∞)
    (hi : cs.IsLeftDescent z i) : φ (f i * z) ≤ φ z := by
  fin_cases i
  · cases z with
    | r k =>
      simp only [f, s0, getDegree_r, Degreele_le_def, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add, getDegree_sr]
      let k' : ℤ := k
      have hk : 0 < k' := by simpa [k'] using left_descent_0_r_pos k hi
      change (k' - 1).natAbs ≤ k'.natAbs ∧ k'.natAbs ≤ k'.natAbs
      exact ⟨natAbs_sub_one_le_self_of_pos hk, le_rfl⟩
    | sr k =>
      simp only [f, s0, getDegree_sr, Degreele_le_def, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, sr_mul_sr, sub_zero, getDegree_r, le_refl, and_true]
      let k' : ℤ := k
      have hk : k' ≤ 0 := by simpa [k'] using left_descent_0_sr_nonpos k hi
      change k'.natAbs ≤ (k' - 1).natAbs
      exact natAbs_le_natAbs_sub_one_of_nonpos hk
  · cases z with
    | r k =>
      simp only [f, s1, getDegree_r, Degreele_le_def, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, sr_mul_r, getDegree_sr]
      let k' : ℤ := k
      have hk : k' < 0 := by simpa [k'] using left_descent_1_r_neg k hi
      change ((1 + k') - 1).natAbs ≤ k'.natAbs ∧ (1 + k').natAbs ≤ k'.natAbs
      exact ⟨by rw [natAbs_one_add_sub_one], natAbs_add_one_le_self_of_neg hk⟩
    | sr k =>
      simp only [f, s1, getDegree_sr, Degreele_le_def, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, sr_mul_sr, getDegree_r]
      let k' : ℤ := k
      have hk : 0 < k' := by simpa [k'] using left_descent_1_sr_pos k hi
      change (k' - 1).natAbs ≤ (k' - 1).natAbs ∧ (k' - 1).natAbs ≤ k'.natAbs
      exact ⟨le_rfl, natAbs_sub_one_le_self_of_pos hk⟩

lemma ends_in_s0_of_not_reduced_descent_0 (u z : D∞)
    (h_nr : ℓ (u * z) < ℓ u + ℓ z) (hi : cs.IsLeftDescent z (0 : Fin 2)) :
    ends_in_s0 u := by
  cases u with
  | r ku =>
    cases z with
    | r kz =>
      simp only [r_mul_r, length_r] at h_nr
      rw [ends_in_s0_r]
      have := left_descent_0_r_pos kz hi
      by_contra! h
      omega
    | sr kz =>
      simp only [r_mul_sr, length_r, length_sr] at h_nr
      rw [ends_in_s0_r]
      have := left_descent_0_sr_nonpos kz hi
      by_contra! h
      split_ifs at h_nr <;> omega
  | sr ku =>
    cases z with
    | r kz =>
      have := left_descent_0_r_pos kz hi
      rw [ends_in_s0_sr]
      simp only [sr_mul_r, length_sr, length_r] at h_nr
      by_contra! h
      split_ifs at h_nr with h_sum_pos
      · omega
      · push Not at h_sum_pos
        omega
    | sr kz =>
      simp only [sr_mul_sr, length_r, length_sr] at h_nr
      rw [ends_in_s0_sr]
      have := left_descent_0_sr_nonpos kz hi
      by_contra! h
      split_ifs at h_nr with h1 h2 <;> omega

lemma not_ends_in_s0_of_not_reduced_descent_1 (u z : D∞)
    (h_nr : ℓ (u * z) < ℓ u + ℓ z) (hi : cs.IsLeftDescent z (1 : Fin 2)) :
    ¬ends_in_s0 u := by
  cases u with
  | r ku =>
    cases z with
    | r kz =>
      simp only [r_mul_r, length_r] at h_nr
      simp only [ends_in_s0_r, not_lt]
      have := left_descent_1_r_neg kz hi
      by_contra! h
      have := Int.natAbs_add_of_nonpos (le_of_lt h) (le_of_lt this)
      omega
    | sr kz =>
      simp only [r_mul_sr, length_r, length_sr] at h_nr
      simp only [ends_in_s0_r, not_lt]
      have := left_descent_1_sr_pos kz hi
      by_contra! h
      split_ifs at h_nr with h1 <;> omega
  | sr ku =>
    cases z with
    | r kz =>
      simp only [sr_mul_r, length_sr, length_r] at h_nr
      simp only [ends_in_s0_sr, not_le]
      have := left_descent_1_r_neg kz hi
      by_contra! h
      have := Int.natAbs_add_of_nonpos h (le_of_lt this)
      split_ifs at h_nr <;> omega
    | sr kz =>
      simp only [sr_mul_sr, length_sr, length_r] at h_nr
      simp only [ends_in_s0_sr, not_le]
      have := left_descent_1_sr_pos kz hi
      by_contra! h
      split_ifs at h_nr with h1 <;> omega

lemma starts_with_s1_of_s0_mul (z : D∞)
    (hi : cs.IsLeftDescent z (0 : Fin 2)) (hne : f 0 * z ≠ 1) :
    starts_with_s1 (f 0 * z) := by
  cases z with
  | r k =>
    simp only [f, s0, Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add]
    rw [starts_with_s1_sr]
    exact left_descent_0_r_pos k hi
  | sr k =>
    simp only [f, s0, Fin.isValue, Matrix.cons_val_zero,
      sr_mul_sr, sub_zero] at hne ⊢
    rw [starts_with_s1_r]
    have hle := left_descent_0_sr_nonpos k hi
    have hne0 : k ≠ 0 := by
      intro h
      apply hne
      rw [h]
      exact r_zero
    exact Std.lt_of_le_of_ne hle hne0

lemma not_starts_with_s1_of_s1_mul (z : D∞)
    (hi : cs.IsLeftDescent z (1 : Fin 2)) :
    ¬starts_with_s1 (f 1 * z) := by
  cases z with
  | r k =>
    simp only [f, s1, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sr_mul_r]
    intro h
    rw [starts_with_s1_sr] at h
    have := left_descent_1_r_neg k hi
    omega
  | sr k =>
    simp only [f, s1, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sr_mul_sr]
    intro h
    rw [starts_with_s1_r] at h
    have := left_descent_1_sr_pos k hi
    omega

lemma length_add_of_not_ends_s0_not_starts_s1 (u v : Vertex)
    (hu : ¬ends_in_s0 u) (hv : ¬starts_with_s1 v) : ℓ (u * v) = ℓ u + ℓ v := by
  cases u with
  | r ku =>
    simp only [ends_in_s0_r, not_lt] at hu
    cases v with
    | r kv =>
      simp only [starts_with_s1_r, not_lt] at hv
      simp only [r_mul_r, length_r]
      omega
    | sr kv =>
      simp only [starts_with_s1_sr, gt_iff_lt, not_lt] at hv
      simp only [r_mul_sr, length_r, length_sr]
      split_ifs <;> omega
  | sr ku =>
    simp only [ends_in_s0_sr, not_le] at hu
    cases v with
    | r kv =>
      simp only [starts_with_s1_r, not_lt] at hv
      simp only [sr_mul_r, length_sr, length_r]
      split_ifs <;> omega
    | sr kv =>
      simp only [starts_with_s1_sr, gt_iff_lt, not_lt] at hv
      simp only [sr_mul_sr, length_sr, length_r]
      split_ifs <;> omega

theorem inv_mul_mem_ad_curve_nbhd (u v : Vertex) (d : Degree) (hv : v ∈ CurveNeighborhood u d) :
    (u⁻¹ * v) ∈ Ad u d := by
  constructor
  · by_cases hu_1 : u = 1
    · simp [hu_1]
    · by_contra h_eq1
      simp only [mul_inv_cancel_left] at h_eq1
      set w := u⁻¹ * v with hw_def
      have h_le : ℓ v ≤ ℓ u + ℓ w := by
        calc
          ℓ v = ℓ (u * w) := by simp [hw_def]
          _ ≤ ℓ u + ℓ w := length_mul_le u w
      have h_lt : ℓ v < ℓ u + ℓ w := lt_of_le_of_ne h_le h_eq1
      have h_u_le_v : ℓ u ≤ ℓ v :=
        CurveNeighborhood_max hv u ⟨0, HasChain.refl u, by
          simp only [Degreele_le_def]; constructor <;> exact le_of_ble_eq_true rfl⟩
      have h_inv_len : ℓ u⁻¹ = ℓ u := (length_inv_eq u).symm
      have h_inv_le : ℓ u⁻¹ ≤ ℓ v := h_inv_len.trans_le h_u_le_v
      have h_dichotomy := length_mul_eq_add_or_sub u⁻¹ v h_inv_le
      rcases h_dichotomy with (h_add | h_sub)
      · rw [h_inv_len] at h_add
        have h_Gamma_nonempty : (CurveNeighborhood 1 d).Nonempty := by
          rw [curve_nbhd_one]
          split_ifs with h
          · exact ⟨s0s1_pow d.a, Set.mem_insert _ _⟩
          · exact ⟨s_alpha_d d, Set.mem_singleton _⟩
        obtain ⟨z, hz⟩ := h_Gamma_nonempty
        have hz_Ad : z ∈ Ad 1 d := by
          rw [curve_nbhd_one_eq_max_ad_one] at hz
          exact hz.1
        have h_uz_le_v : ℓ (u * z) ≤ ℓ v := len_mul_ad_le_curve_nbhd_max u d z v hz_Ad hv
        have h_w_le_z : ℓ w ≤ ℓ z := inv_mul_len_le_curve_nbhd_one_max u d z v hz hv
        have h_uv_le_z : ℓ u + ℓ v ≤ ℓ z := by
          rw [← h_add]
          exact h_w_le_z
        have h_uz_not_reduced : ℓ (u * z) < ℓ u + ℓ z := by omega
        have h_u_pos : ℓ u ≥ 1 := by
          by_contra! h
          have : ℓ u = 0 := lt_one_iff.mp h
          exact hu_1 ((length_eq_zero_iff cs).mp this)
        have hz_ne : z ≠ 1 := by
          intro h
          rw [h, cs.length_one] at h_uv_le_z
          omega
        have h_exists_z' : ∃ z' ∈ Ad 1 d, ℓ z' = ℓ z - 1 ∧ ℓ (u * z') = ℓ u + ℓ z' := by
          obtain ⟨i, hi_left⟩ := cs.exists_leftDescent_of_ne_one hz_ne
          set z' := cs.simple i * z with hz'_def
          use z'
          have hs : cs.simple i = f i := by
            fin_cases i <;> rfl
          have h_z'_len : ℓ z' = ℓ z - 1 := by
            rw [cs.isLeftDescent_iff] at hi_left
            calc
              ℓ z' = ℓ (cs.simple i * z) := by rw [hz'_def]
              _ = ℓ z - 1 := Nat.eq_sub_of_add_eq hi_left
          have h_z'_deg : φ z' ≤ d := by
            have : φ z' ≤ φ z := by
              rw [hz'_def, hs]
              exact degree_le_of_left_descent i z hi_left
            exact le_trans this hz_Ad.2
          have h_prod : ℓ (u * z') = ℓ u + ℓ z' := by
            by_cases hz'_one : z' = 1
            · simp [hz'_one]
            · rw [hs] at hz'_def
              fin_cases i
              · exact length_add_of_ends_s0_starts_s1 u z'
                  (ends_in_s0_of_not_reduced_descent_0 u z h_uz_not_reduced hi_left)
                  (by
                    rw [hz'_def]
                    exact starts_with_s1_of_s0_mul z hi_left (fun h => hz'_one (hz'_def.trans h)))
              · exact length_add_of_not_ends_s0_not_starts_s1 u z'
                  (not_ends_in_s0_of_not_reduced_descent_1 u z h_uz_not_reduced hi_left)
                  (by
                    rw [hz'_def]
                    exact not_starts_with_s1_of_s1_mul z hi_left)
          refine ⟨?_, h_z'_len, h_prod⟩
          simp only [Ad, one_mul, length_one, zero_add, true_and, Set.mem_setOf_eq]
          exact h_z'_deg
        obtain ⟨z', hz'_Ad, hz'_len, hz'_reduced⟩ := h_exists_z'
        have h_uz'_le_v : ℓ (u * z') ≤ ℓ v := len_mul_ad_le_curve_nbhd_max u d z' v hz'_Ad hv
        omega
      · rw [h_inv_len, ← hw_def] at h_sub
        have : ℓ v = ℓ u + ℓ w := (Nat.sub_eq_iff_eq_add' h_u_le_v).mp (id (Eq.symm h_sub))
        contradiction
  · exact deg_inv_mul_le_curve_nbhd u d v hv

lemma Ad_u_in_Ad_one (u : Vertex) (d : Degree) (v : Vertex) (h : v ∈ Ad u d) : v ∈ Ad 1 d := by
  rw [Ad] at *
  simp only [one_mul, cs.length_one, zero_add, Set.mem_setOf_eq]
  exact And.imp_left (fun a ↦ trivial) h

lemma exists_max_in_Ad (u : Vertex) (d : Degree) (z : Vertex) (hz : z ∈ Ad u d) :
    ∃ w, IsMaximalIn w (Ad u d) ∧ z ≤ w := by
  let S_ge_z := { w ∈ Ad u d | z ≤ w }
  have h_fin : S_ge_z.Finite := ad_finite.subset (Set.sep_subset _ _)
  have h_nonempty : S_ge_z.Nonempty := ⟨z, hz, le_refl z⟩
  obtain ⟨m, ⟨hm_in_Ad, h_z_le_m⟩, hm_max_in_subset⟩ :=
    Set.Finite.exists_maximalFor (id) S_ge_z h_fin h_nonempty
  use m
  constructor
  · refine ⟨hm_in_Ad, fun v' hv' hm_le_v' => ?_⟩
    have h_v'_in_subset : v' ∈ S_ge_z := ⟨hv', le_trans h_z_le_m hm_le_v'⟩
    have := hm_max_in_subset h_v'_in_subset hm_le_v'
    simp only [id_eq] at this
    exact le_antisymm hm_le_v' this
  · exact h_z_le_m

lemma reachable_of_Ad (u : Vertex) (d : Degree) (w : Vertex) (h : w ∈ Ad u d) :
    u * w ∈ ReachableSet u d := by
  have c2 := chain_left_mul u 1 w (getDegree w) (trivial_chain w)
  simp only [mul_one] at c2
  exact ⟨getDegree w, c2, h.2⟩

lemma mul_le_mul_left_of_length_add (u : Vertex) (x y : Vertex)
    (hx : ℓ (u * x) = ℓ u + ℓ x) (hy : ℓ (u * y) = ℓ u + ℓ y) :
    x ≤ y ↔ u * x ≤ u * y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lt_iff_length_lt, lt_iff_length_lt, hx, hy]
  constructor
  · rintro (h | rfl)
    · left; omega
    · right; rfl
  · rintro (h | h)
    · left; omega
    · right; exact mul_left_cancel h

lemma Lt_iff_le_and_ne (a b : Vertex) : Lt a b ↔ a ≤ b ∧ a ≠ b := by
  rw [Lt, le_iff_lt_or_eq]
  constructor
  · intro h
    constructor
    · left; exact h
    · rcases h with ⟨d, chain, ne⟩
      exact ne
  · rintro ⟨(h_lt | h_eq), h_ne⟩
    · exact h_lt
    · contradiction

lemma exists_max_ge_in_Reachable (u : Vertex) (d : Degree) (v : Vertex)
    (h : v ∈ ReachableSet u d) :
    ∃ m, m ∈ CurveNeighborhood u d ∧ v ≤ m := by
  let S_bound := { x : Vertex | φ (u⁻¹ * x) ≤ d }
  have h_bound_finite : S_bound.Finite := by
    let pre_image := { y : Vertex | φ y ≤ d }
    have h_pre_finite : pre_image.Finite := by
      have heq : pre_image = Ad 1 d := (ad_one_eq_degree_le d).symm
      rw [heq]
      exact ad_finite
    have : S_bound = (fun y => u * y) '' pre_image := by
       ext x
       simp [S_bound, pre_image]
    rw [this]
    exact Set.Finite.image _ h_pre_finite
  have h_subset : ReachableSet u d ⊆ S_bound := by
    intro x hx
    rcases hx with ⟨dx, chain, h_dx_le_d⟩
    have chain_inv := chain_left_mul u⁻¹ u x dx chain
    simp only [inv_mul_cancel] at chain_inv
    have h_phi := inv_mul_degree_le_of_chain 1 (u⁻¹ * x) dx
    simp only [inv_one, one_mul] at h_phi
    exact le_trans (h_phi chain_inv) h_dx_le_d
  let S_ge_v := { m ∈ ReachableSet u d | v ≤ m }
  have h_fin_sub : S_ge_v.Finite :=by
    apply Set.Finite.subset h_bound_finite
    intro x ⟨hx_reach, _⟩
    exact h_subset hx_reach
  have h_nonempty : S_ge_v.Nonempty := ⟨v, h, le_refl v⟩
  obtain ⟨m, ⟨hm_reach, h_v_le_m⟩, hm_max⟩ :=
    Set.Finite.exists_maximalFor id S_ge_v h_fin_sub h_nonempty
  use m
  constructor
  · rw [CurveNeighborhood]
    refine ⟨hm_reach, fun v' hv' hm_le_v' => ?_⟩
    have h_v'_in_S : v' ∈ S_ge_v := ⟨hv', le_trans h_v_le_m hm_le_v'⟩
    have := hm_max h_v'_in_S hm_le_v'
    simp only [id_eq] at this
    exact le_antisymm hm_le_v' this
  · exact h_v_le_m

theorem main_theorem (u : Vertex) (d : Degree) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } := by
  apply Set.ext
  intro v
  constructor
  · intro hv
    have h_z_in_Ad : (u⁻¹ * v) ∈ Ad u d := inv_mul_mem_ad_curve_nbhd u v d hv
    let z := u⁻¹ * v
    have h_v_eq : v = u * z := by simp [z]
    obtain ⟨w, hw_max, h_z_le_w⟩ := exists_max_in_Ad u d z h_z_in_Ad
    have hw_in_Ad1 : w ∈ Ad 1 d := Ad_u_in_Ad_one u d w hw_max.1
    have h_len_uw_le_v := len_mul_ad_le_curve_nbhd_max u d w v hw_in_Ad1 hv
    have h_len_v : ℓ v = ℓ u + ℓ z := by
      rw [h_v_eq]
      exact h_z_in_Ad.1
    have h_len_uw : ℓ (u * w) = ℓ u + ℓ w := hw_max.1.1
    rw [h_len_v, h_len_uw] at h_len_uw_le_v
    have h_len_w_le_z : ℓ w ≤ ℓ z := Nat.le_of_add_le_add_left h_len_uw_le_v
    have h_z_eq_w : z = w := by
      by_contra h_neq
      have h_lt : z < w := lt_of_le_of_ne h_z_le_w h_neq
      have h_len_lt : ℓ z < ℓ w := by
        rw [← lt_iff_length_lt]
        exact h_lt
      omega
    use w
    constructor
    · exact hw_max
    · rw [h_v_eq, h_z_eq_w]
  · rintro ⟨w, hw_max, rfl⟩
    have h_reach : u * w ∈ ReachableSet u d := reachable_of_Ad u d w hw_max.1
    rw [CurveNeighborhood]
    refine ⟨h_reach, ?_⟩
    intro v' h_reach_v' h_le_v_v'
    obtain ⟨m, hm_max, h_v'_le_m⟩ := exists_max_ge_in_Reachable u d v' h_reach_v'
    have h_m_in_gamma : m ∈ CurveNeighborhood u d := hm_max
    have h_z'_in_Ad : (u⁻¹ * m) ∈ Ad u d := inv_mul_mem_ad_curve_nbhd u m d h_m_in_gamma
    let w' := u⁻¹ * m
    have h_m_eq : m = u * w' := by simp [w']
    have h_uw_le_uw' : u * w ≤ u * w' :=
        le_trans h_le_v_v' (by rw [h_m_eq] at h_v'_le_m; exact h_v'_le_m)
    have h_w_le_w' : w ≤ w' := by
      rw [← mul_le_mul_left_of_length_add u w w' hw_max.1.1 h_z'_in_Ad.1] at h_uw_le_uw'
      exact h_uw_le_uw'
    have h_w_eq_w' : w = w' :=
      hw_max.2 w' h_z'_in_Ad h_w_le_w'
    have h_v_eq_m : u * w = m := by rw [h_m_eq, ←h_w_eq_w']
    have h_v'_eq_v : v' = u * w := by
      have h_m_eq_uw : m = u * w := h_v_eq_m.symm
      rw [h_m_eq_uw] at h_v'_le_m
      exact le_antisymm h_v'_le_m h_le_v_v'
    rw [h_v'_eq_v]

theorem curve_nbhd_eq_mul_max_ad (u : Vertex) (d : Degree) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } := by
  simpa using main_theorem u d


/-- Paper Lemma 3.4, packaged in the form used by the main theorem. -/
theorem lemma_3_4 (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hzAd : z ∈ Ad 1 d) (hzMax : z ∈ CurveNeighborhood 1 d)
    (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u * z) ≤ ℓ v ∧ φ (u⁻¹ * v) ≤ d ∧ ℓ (u⁻¹ * v) ≤ ℓ z :=
  ⟨len_mul_ad_le_curve_nbhd_max u d z v hzAd hv,
    deg_inv_mul_le_curve_nbhd u d v hv,
    inv_mul_len_le_curve_nbhd_one_max u d z v hzMax hv⟩

/-- Paper-number alias for Lemma 3.5. -/
theorem lemma_3_5 (u v : Vertex) (d : Degree) (hv : v ∈ CurveNeighborhood u d) :
    (u⁻¹ * v) ∈ Ad u d :=
  inv_mul_mem_ad_curve_nbhd u v d hv

/-- Paper-number alias for Theorem 3.6. -/
theorem theorem_3_6 (u : Vertex) (d : Degree) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } :=
  main_theorem u d