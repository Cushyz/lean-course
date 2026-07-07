import Dihedral.Identity
import Dihedral.Mathlib

open CoxeterSystem DihedralGroup Nat

def ends_in_s0 (u : D∞) : Prop := (reducedWord u).getLast? = some 0
def starts_with_s1 (v : D∞) : Prop := (reducedWord v).head? = some 1

lemma reducedWord_r_nonneg (k : ℤ) (hk : k ≥ 0) :
    reducedWord (r k) = alternatingWord 0 1 (2 * k.natAbs) := by
  simp [reducedWord, hk]

lemma reducedWord_r_neg (k : ℤ) (hk : ¬k ≥ 0) :
    reducedWord (r k) = alternatingWord 1 0 (2 * k.natAbs) := by
  simp [reducedWord, hk]

lemma reducedWord_sr_pos (k : ℤ) (hk : k > 0) :
    reducedWord (sr k) = alternatingWord 0 1 (2 * k.natAbs - 1) := by
  simp [reducedWord, hk]

lemma reducedWord_sr_nonpos (k : ℤ) (hk : ¬k > 0) :
    reducedWord (sr k) = alternatingWord 1 0 (2 * k.natAbs + 1) := by
  simp [reducedWord, hk]

lemma s_alpha_starts_with (α : Root) :
    (reducedWord (s_α α)).head? = some (if α.a > α.b then 0 else 1) := by
  unfold s_α
  split_ifs with h
  · rcases α.sub_one with hsub | hsub
    · have h_sum : α.a + α.b = 2 * α.b + 1 := by omega
      rw [h_sum]
      change (reducedWord (cs.wordProd (alternatingWord 1 0 (2 * α.b + 1)))).head? = some 0
      rw [alternating_reducedWord 1 0 (2 * α.b + 1) (by decide)]
      simpa using (alternatingWord_head_odd 1 0 α.b)
    · omega
  · rcases α.sub_one with hsub | hsub
    · omega
    · have h_sum : α.a + α.b = 2 * α.a + 1 := by omega
      rw [h_sum]
      change (reducedWord (cs.wordProd (alternatingWord 0 1 (2 * α.a + 1)))).head? = some 1
      rw [alternating_reducedWord 0 1 (2 * α.a + 1) (by decide)]
      simpa using (alternatingWord_head_odd 0 1 α.a)

lemma ends_in_s0_r (k : ℤ) : ends_in_s0 (r k) ↔ k < 0 := by
  unfold ends_in_s0
  constructor
  · intro h
    by_cases hk : k ≥ 0
    · rw [reducedWord_r_nonneg k hk] at h
      by_cases hk0 : k = 0
      · subst hk0
        exfalso
        simp [alternatingWord] at h
      · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
        have hlast := alternatingWord_getLast_pos 0 1 (2 * k.natAbs) (by omega)
        rw [hlast] at h
        exfalso
        simp at h
    · exact lt_of_not_ge hk
  · intro hk
    rw [reducedWord_r_neg k (not_le.mpr hk)]
    have hlast := alternatingWord_getLast_pos 1 0 (2 * k.natAbs) (by omega)
    simp [hlast]

lemma ends_in_s0_sr (k : ℤ) : ends_in_s0 (sr k) ↔ k ≤ 0 := by
  unfold ends_in_s0
  constructor
  · intro h
    by_cases hk : k > 0
    · rw [reducedWord_sr_pos k hk] at h
      have hlast := alternatingWord_getLast_pos 0 1 (2 * k.natAbs - 1) (by omega)
      rw [hlast] at h
      exfalso
      simp at h
    · exact le_of_not_gt hk
  · intro hk
    rw [reducedWord_sr_nonpos k (not_lt.mpr hk)]
    have hlast := alternatingWord_getLast_pos 1 0 (2 * k.natAbs + 1) (by omega)
    simp [hlast]

lemma starts_with_s1_r (k : ℤ) : starts_with_s1 (r k) ↔ k < 0 := by
  unfold starts_with_s1
  constructor
  · intro h
    by_cases hk : k ≥ 0
    · rw [reducedWord_r_nonneg k hk] at h
      by_cases hk0 : k = 0
      · subst hk0
        exfalso
        simp [alternatingWord] at h
      · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
        have hhead := alternatingWord_head_even_pos 0 1 k.natAbs hpos
        rw [hhead] at h
        exfalso
        simp at h
    · exact lt_of_not_ge hk
  · intro hk
    rw [reducedWord_r_neg k (not_le.mpr hk)]
    have hk0 : k ≠ 0 := ne_of_lt hk
    have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
    have hhead := alternatingWord_head_even_pos 1 0 k.natAbs hpos
    simp [hhead]

lemma starts_with_s1_sr (k : ℤ) : starts_with_s1 (sr k) ↔ k > 0 := by
  unfold starts_with_s1
  constructor
  · intro h
    by_cases hk : k > 0
    · exact hk
    · rw [reducedWord_sr_nonpos k hk] at h
      have hhead := alternatingWord_head_odd 1 0 k.natAbs
      rw [hhead] at h
      exfalso
      simp at h
  · intro hk
    rw [reducedWord_sr_pos k hk]
    have hhead := alternatingWord_head_odd 0 1 (k.natAbs - 1)
    have hlen : 2 * k.natAbs - 1 = 2 * (k.natAbs - 1) + 1 := by omega
    simpa [hlen] using hhead

lemma length_add_of_ends_s0_starts_s1 (u v : Vertex)
    (hu : ends_in_s0 u) (hv : starts_with_s1 v) : ℓ (u * v) = ℓ u + ℓ v := by
  cases u with
  | r ku =>
    let ku' : ℤ := ku
    have hu' : ku' < 0 := by
      have : ends_in_s0 (r ku') := hu
      exact (ends_in_s0_r ku').mp this
    cases v with
    | r kv =>
      let kv' : ℤ := kv
      have hv' : kv' < 0 := by
        have : starts_with_s1 (r kv') := hv
        exact (starts_with_s1_r kv').mp this
      simp only [r_mul_r, length_r]
      change 2 * Int.natAbs (ku' + kv') = 2 * Int.natAbs ku' + 2 * Int.natAbs kv'
      have h : (ku' + kv').natAbs = ku'.natAbs + kv'.natAbs :=
        Int.natAbs_add_of_nonpos (le_of_lt hu') (le_of_lt hv')
      rw [h]
      ring
    | sr kv =>
      let kv' : ℤ := kv
      have hv' : kv' > 0 := by
        have : starts_with_s1 (sr kv') := hv
        exact (starts_with_s1_sr kv').mp this
      have h_pos : kv' - ku' > 0 := by linarith
      have h_natAbs : (kv' - ku').natAbs = kv'.natAbs + ku'.natAbs := by
        rw [show kv' - ku' = kv' + (-ku') by ring,
          Int.natAbs_add_of_nonneg (le_of_lt hv') (by linarith : (0 : ℤ) ≤ -ku'),
          Int.natAbs_neg]
      simp only [r_mul_sr, length_r, length_sr]
      split_ifs with h1
      · change 2 * Int.natAbs (kv' - ku') - 1 =
          2 * Int.natAbs ku' + (2 * Int.natAbs kv' - 1)
        rw [h_natAbs]
        omega
      · exfalso
        exact h1 h_pos
  | sr ku =>
    let ku' : ℤ := ku
    have hu' : ku' ≤ 0 := by
      have : ends_in_s0 (sr ku') := hu
      exact (ends_in_s0_sr ku').mp this
    have h_u_not_pos : ¬(ku' > 0) := not_lt.mpr hu'
    cases v with
    | r kv =>
      let kv' : ℤ := kv
      have hv' : kv' < 0 := by
        have : starts_with_s1 (r kv') := hv
        exact (starts_with_s1_r kv').mp this
      have h_sum_not_pos : ¬(ku' + kv' > 0) := by linarith
      have h_natAbs : (ku' + kv').natAbs = ku'.natAbs + kv'.natAbs :=
        Int.natAbs_add_of_nonpos hu' (le_of_lt hv')
      simp only [sr_mul_r, length_sr, length_r]
      split_ifs with h1
      · exfalso
        exact h_sum_not_pos h1
      · change 2 * Int.natAbs (ku' + kv') + 1 =
          2 * Int.natAbs ku' + 1 + 2 * Int.natAbs kv'
        rw [h_natAbs]
        omega
    | sr kv =>
      let kv' : ℤ := kv
      have hv' : kv' > 0 := by
        have : starts_with_s1 (sr kv') := hv
        exact (starts_with_s1_sr kv').mp this
      have h_natAbs : (kv' - ku').natAbs = kv'.natAbs + ku'.natAbs := by
        rw [show kv' - ku' = kv' + (-ku') by ring,
          Int.natAbs_add_of_nonneg (le_of_lt hv') (by linarith : (0 : ℤ) ≤ -ku'),
          Int.natAbs_neg]
      simp only [sr_mul_sr, length_r, length_sr]
      split_ifs with h1
      · exfalso
        exact h_u_not_pos h1
      · change 2 * Int.natAbs (kv' - ku') =
          2 * Int.natAbs ku' + 1 + (2 * Int.natAbs kv' - 1)
        rw [h_natAbs]
        omega

lemma not_length_add_of_ends_s0_mul_r_pos (u : Vertex) (k : ℤ)
    (hu : ends_in_s0 u) (hk : 0 < k) :
    ℓ (u * r k) ≠ ℓ u + ℓ (r k) := by
  cases u with
  | r m =>
    let m' : ℤ := m
    have hm : m' < 0 := (ends_in_s0_r m').mp hu
    have hlen_u : ℓ (r m') = 2 * m'.natAbs := by simp [length_r]
    have hlen_v : ℓ (r k) = 2 * k.natAbs := by simp [length_r]
    have hlen_prod : ℓ (r m' * r k) = 2 * (m' + k).natAbs := by
      simp [r_mul_r, length_r]
      rfl
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    have h_abs : (m' + k).natAbs ≤ m'.natAbs + k.natAbs := Int.natAbs_add_le m' k
    omega
  | sr m =>
    let m' : ℤ := m
    have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
    have hlen_u : ℓ (sr m') = 2 * m'.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hm]
    have hlen_v : ℓ (r k) = 2 * k.natAbs := by simp [length_r]
    have hlen_prod : ℓ (sr m' * r k)
        = (if m' + k > 0 then 2 * (m' + k).natAbs - 1 else 2 * (m' + k).natAbs + 1) := by
      simp [sr_mul_r, length_sr]
      rfl
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    split_ifs at heq with hmk
    · have h_abs : (m' + k).natAbs ≤ m'.natAbs + k.natAbs := Int.natAbs_add_le m' k
      omega
    · have h_abs : (m' + k).natAbs ≤ m'.natAbs + k.natAbs := Int.natAbs_add_le m' k
      omega

lemma not_length_add_of_ends_s0_mul_sr_nonpos (u : Vertex) (k : ℤ)
    (hu : ends_in_s0 u) (hk : k ≤ 0) :
    ℓ (u * sr k) ≠ ℓ u + ℓ (sr k) := by
  cases u with
  | r m =>
    let m' : ℤ := m
    have hm : m' < 0 := (ends_in_s0_r m').mp hu
    have hlen_u : ℓ (r m') = 2 * m'.natAbs := by simp [length_r]
    have hlen_v : ℓ (sr k) = 2 * k.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hk]
    have hlen_prod : ℓ (r m' * sr k)
        = (if k - m' > 0 then 2 * (k - m').natAbs - 1 else 2 * (k - m').natAbs + 1) := by
      rw [r_mul_sr, length_sr]
      split_ifs <;> omega
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    split_ifs at heq with hkm
    · have h_abs : (k - m').natAbs ≤ k.natAbs + m'.natAbs := Int.natAbs_sub_le k m'
      omega
    · have h_abs : (k - m').natAbs ≤ k.natAbs + m'.natAbs := Int.natAbs_sub_le k m'
      omega
  | sr m =>
    let m' : ℤ := m
    have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
    have hlen_u : ℓ (sr m') = 2 * m'.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hm]
    have hlen_v : ℓ (sr k) = 2 * k.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hk]
    have hlen_prod : ℓ (sr m' * sr k) = 2 * (k - m').natAbs := by
      simp [sr_mul_sr, length_r]
      rfl
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    have h_abs : (k - m').natAbs ≤ k.natAbs + m'.natAbs := Int.natAbs_sub_le k m'
    omega

theorem max_ad_b_gt_a_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.b > d.a) : IsMaximalIn (s_alpha_d d) (Ad u d) := by
  set w := s_alpha_d d with hw_def
  have hna : ¬(d.a > d.b) := not_lt.mpr (le_of_lt h)
  have h_root : root_from_degree d = ⟨d.a, d.a + 1, Or.inr rfl⟩ := by
    unfold root_from_degree
    simp only [hna, ↓reduceIte]
  have hw_eq : w = cs.wordProd (alternatingWord 0 1 (2 * d.a + 1)) := by
    rw [hw_def]
    unfold s_alpha_d s_α
    rw [h_root]
    have hnot : ¬d.a > d.a + 1 := Nat.not_lt.mpr (Nat.le_add_right d.a 1)
    have hsum : d.a + (d.a + 1) = 2 * d.a + 1 := by omega
    simp [hnot, hsum]
  have hw_sr : w = sr ((d.a : ℤ) + 1) := by
    rw [hw_eq, cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * d.a + 1)]
    have h_div : (2 * d.a + 1) / 2 = d.a := by omega
    simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr,
      sub_zero, h_div, r_pow, one_mul, sr_mul_r]
    simp [add_comm]
    rfl
  have hw_starts_s1 : starts_with_s1 w := by
    rw [hw_sr, starts_with_s1_sr]
    omega
  have h_len : ℓ (u * w) = ℓ u + ℓ w :=
    length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
  have h_deg : φ w ≤ d := by
    rw [hw_def]
    unfold s_alpha_d
    rw [h_root, φ_s_alpha_eq]
    simp only [Root.toDegree, Degreele_le_def, le_refl]
    constructor
    · trivial
    · exact h
  have hw_len : ℓ w = 2 * d.a + 1 := by
    rw [hw_sr, length_sr_abs]
    simp
    omega
  have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * d.a + 1 := by
    intro v ⟨_, hv_deg⟩
    cases v with
    | r k =>
      simp only [getDegree_r, Degreele_le_def] at hv_deg
      simp only [length_r]
      calc
        2 * k.natAbs ≤ 2 * d.a := Nat.mul_le_mul_left 2 hv_deg.1
        _ ≤ 2 * d.a + 1 := Nat.le_succ _
    | sr k =>
      simp only [getDegree_sr, Degreele_le_def] at hv_deg
      simp only [length_sr]
      split_ifs with hk
      · have hk_sub : (((k.cast : ℤ) - 1).natAbs) = (k.cast : ℤ).natAbs - 1 :=
          natAbs_sub_one_of_pos (k := (k.cast : ℤ)) hk
        rw [hk_sub] at hv_deg
        change 2 * (k.cast : ℤ).natAbs - 1 ≤ 2 * d.a + 1
        omega
      · have hk_sub : (((k.cast : ℤ) - 1).natAbs) = (k.cast : ℤ).natAbs + 1 :=
          natAbs_sub_one_of_nonpos (k := (k.cast : ℤ)) hk
        rw [hk_sub] at hv_deg
        change 2 * (k.cast : ℤ).natAbs + 1 ≤ 2 * d.a + 1
        omega
  constructor
  · exact ⟨h_len, h_deg⟩
  · intro v hv hv_le
    rcases hv_le with hv_lt | hv_eq
    · have hlen_lt : ℓ w < ℓ v := (lt_iff_length_lt w v).mp hv_lt
      have hlen_bound := hv_len_bound v hv
      rw [hw_len] at hlen_lt
      omega
    · exact hv_eq

theorem max_ad_a_gt_b_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.a > d.b) : IsMaximalIn (s0 * s_alpha_d d) (Ad u d) := by
  set w := s0 * s_alpha_d d with hw_def
  have h_root : root_from_degree d = ⟨d.b + 1, d.b, Or.inl rfl⟩ := by
    unfold root_from_degree
    simp only [h, ↓reduceIte]
  have hs_alpha : s_alpha_d d = sr (-(d.b : ℤ)) := by
    unfold s_alpha_d s_α
    rw [h_root]
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, Fin.isValue]
    have h_sum : d.b + 1 + d.b = 2 * d.b + 1 := by ring
    rw [h_sum, cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * d.b + 1)]
    have h_div : (2 * d.b + 1) / 2 = d.b := by omega
    simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
      zero_sub, h_div, r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
    rfl
  have hw_r : w = r (-(d.b : ℤ)) := by
    rw [hw_def, hs_alpha]
    simp [s0, sr_mul_sr]
  by_cases hb_pos : d.b > 0
  · have hw_starts_s1 : starts_with_s1 w := by
      rw [hw_r, starts_with_s1_r]
      simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact hb_pos
    have h_len : ℓ (u * w) = ℓ u + ℓ w :=
      length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
    have h_deg : φ w ≤ d := by
      rw [hw_r]
      rw [getDegree_r_neg_natCast]
      simp only [Degreele_le_def]
      exact ⟨le_of_lt h, le_rfl⟩
    have hw_len : ℓ w = 2 * d.b := by
      rw [hw_r, length_r]
      simp
    have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * d.b := by
      intro v ⟨hv_len_eq, hv_deg⟩
      cases v with
      | r k =>
        simp only [getDegree_r, Degreele_le_def] at hv_deg
        simp only [length_r]
        exact Nat.mul_le_mul_left 2 hv_deg.2
      | sr k =>
        simp only [getDegree_sr, Degreele_le_def] at hv_deg
        simp only [length_sr]
        split_ifs with hk
        · rcases hv_deg with ⟨_, h_les⟩
          calc 2 * k.natAbs - 1
            _ ≤ 2 * k.natAbs := Nat.sub_le _ _
            _ ≤ 2 * d.b := Nat.mul_le_mul_left 2 h_les
        · exfalso
          let k' : ℤ := k
          have hk' : k' ≤ 0 := by
            simpa [k', gt_iff_lt] using hk
          have hv_len_eq' : ℓ (u * sr k') = ℓ u + ℓ (sr k') := by
            simpa [k'] using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_sr_nonpos u k' hu hk') hv_len_eq'
    constructor
    · exact ⟨h_len, h_deg⟩
    · intro v hv hv_le
      rcases hv_le with hv_lt | hv_eq
      · have hlen_lt : ℓ w < ℓ v := (lt_iff_length_lt w v).mp hv_lt
        have hlen_bound := hv_len_bound v hv
        rw [hw_len] at hlen_lt
        omega
      · exact hv_eq
  · have hb_zero : d.b = 0 := Nat.eq_zero_of_not_pos hb_pos
    have hw_one : w = 1 := by
      rw [hw_r, hb_zero]
      simp
      rfl
    have hv_one : ∀ v, v ∈ Ad u d → v = 1 := by
      intro v ⟨hv_len_eq, hv_deg⟩
      have hv_len_zero : ℓ v = 0 := by
        cases v with
        | r k =>
          simp only [getDegree_r, Degreele_le_def, hb_zero] at hv_deg
          simp only [length_r]
          have : k.natAbs ≤ 0 := hv_deg.2
          have : k.natAbs = 0 := Nat.eq_zero_of_le_zero this
          linarith
        | sr k =>
          exfalso
          simp only [getDegree_sr, Degreele_le_def, hb_zero] at hv_deg
          rcases hv_deg with ⟨_, h⟩
          have hk_zero : k.natAbs = 0 := Nat.eq_zero_of_le_zero h
          have hk_eq : k = 0 := Int.natAbs_eq_zero.mp hk_zero
          subst hk_eq
          have hv_len_eq' : ℓ (u * sr (0 : ℤ)) = ℓ u + ℓ (sr (0 : ℤ)) := by
            exact hv_len_eq
          exact (not_length_add_of_ends_s0_mul_sr_nonpos u (0 : ℤ) hu (by omega)) hv_len_eq'
      exact (length_eq_zero_iff cs).mp hv_len_zero
    rw [hw_one]
    constructor
    · constructor
      · simp
      · simp only [Degreele_le_def]
        exact ⟨Nat.zero_le d.a, Nat.zero_le d.b⟩
    · intro v hv hv_le
      symm
      exact hv_one v hv

theorem max_ad_a_eq_b_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.a = d.b) : IsMaximalIn (s1 * s_alpha_d (d.sub {a := 0, b := 1})) (Ad u d) := by
  set a := d.a with ha_def
  set w := s1 * s_alpha_d (d.sub {a := 0, b := 1}) with hw_def
  by_cases ha_pos : a > 0
  · have h_dsub : d.sub {a := 0, b := 1} = ⟨a, a - 1⟩ := by
      simp only [Degree.sub, h, Nat.sub_zero]
      ext <;> simp only
      exact h
    have h_a_gt : a > a - 1 := Nat.sub_lt ha_pos (by omega)
    have h_root : root_from_degree (d.sub {a := 0, b := 1}) = ⟨a, a - 1, Or.inl (by omega)⟩ := by
      unfold root_from_degree
      rw [h_dsub]
      simp only [h_a_gt, ↓reduceIte]
      congr
      exact Nat.sub_add_cancel ha_pos
    have hs_alpha : s_alpha_d (d.sub {a := 0, b := 1}) = sr (1 - (a : ℤ)) := by
      unfold s_alpha_d s_α
      rw [h_root]
      simp only [gt_iff_lt, h_a_gt, ↓reduceIte, Fin.isValue]
      rw [show a + (a - 1) = 2 * (a - 1) + 1 by omega]
      rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * (a - 1) + 1)]
      have h_div : (2 * (a - 1) + 1) / 2 = a - 1 := two_mul_add_one_div_two (a - 1)
      simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
        zero_sub, h_div, r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
      apply congrArg sr
      have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
        exact Nat.cast_sub (by omega : 1 ≤ a)
      change -(((a - 1 : ℕ) : ℤ)) = 1 - (a : ℤ)
      rw [hcast]
      ring_nf
    have hw_r : w = r (-(a : ℤ)) := by
      rw [hw_def, hs_alpha, s1, sr_mul_sr]
      apply congrArg r
      change ((1 - (a : ℤ) - 1 : ℤ) : ZMod 0) = (-(a : ℤ) : ZMod 0)
      ring_nf
    have hw_starts_s1 : starts_with_s1 w := by
      rw [hw_r, starts_with_s1_r]
      simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact ha_pos
    have h_len : ℓ (u * w) = ℓ u + ℓ w :=
      length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
    have h_deg : φ w ≤ d := by
      rw [hw_r]
      rw [getDegree_r_neg_natCast]
      simp only [Degreele_le_def]
      exact ⟨le_of_eq ha_def.symm, le_of_eq h⟩
    have hw_len : ℓ w = 2 * a := by
      rw [hw_r, length_r]
      simp
    have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * a := by
      intro v ⟨hv_len_eq, hv_deg⟩
      cases v with
      | r k =>
        let k' : ℤ := k
        by_cases hk_sign : 0 < k'
        · exfalso
          have hv_len_eq' : ℓ (u * r k') = ℓ u + ℓ (r k') := by
            simpa [k'] using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_r_pos u k' hu hk_sign) hv_len_eq'
        · simp only [getDegree_r, Degreele_le_def] at hv_deg
          simp only [length_r]
          exact Nat.mul_le_mul_left 2 hv_deg.1
      | sr k =>
        let k' : ℤ := k
        by_cases hk_pos : k' > 0
        · simp only [length_sr]
          simp only [getDegree_sr, Degreele_le_def] at hv_deg
          have h1 : 2 * k'.natAbs - 1 ≤ 2 * k'.natAbs := Nat.sub_le _ _
          have hk_le_a : k'.natAbs ≤ a := by
            simpa [k', h.symm] using hv_deg.2
          have h2 : 2 * k'.natAbs ≤ 2 * a := Nat.mul_le_mul_left 2 hk_le_a
          split_ifs <;> omega
        · exfalso
          have hk_le : k' ≤ 0 := not_lt.mp hk_pos
          have hv_len_eq' : ℓ (u * sr k') = ℓ u + ℓ (sr k') := by
            simpa [k'] using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_sr_nonpos u k' hu hk_le) hv_len_eq'
    constructor
    · exact ⟨h_len, h_deg⟩
    · intro v hv hv_le
      rcases hv_le with hv_lt | hv_eq
      · have hlen_lt : ℓ w < ℓ v := (lt_iff_length_lt w v).mp hv_lt
        have hlen_bound := hv_len_bound v hv
        rw [hw_len] at hlen_lt
        omega
      · exact hv_eq
  · have ha_zero : a = 0 := Nat.eq_zero_of_not_pos ha_pos
    have hd_zero : d = ⟨0, 0⟩ := by
      ext <;> simp only
      · exact ha_zero
      · rw [← h, ha_zero]
    have h_dsub : d.sub {a := 0, b := 1} = ⟨0, 0⟩ := by
      rw [hd_zero]
      rfl
    have hs_alpha : s_alpha_d (d.sub {a := 0, b := 1}) = s1 := by
      rw [h_dsub]
      decide
    have hw_one : w = 1 := by
      rw [hw_def, hs_alpha, s1]
      simp
    rw [hw_one]
    have hv_must_be_one : ∀ v, v ∈ Ad u d → v = 1 := by
      intro v ⟨hv_len_eq, hv_deg⟩
      rw [hd_zero] at hv_deg
      simp only [Degreele_le_def] at hv_deg
      have ha_zero' : (φ v).a = 0 := Nat.eq_zero_of_le_zero hv_deg.1
      have hb_zero : (φ v).b = 0 := Nat.eq_zero_of_le_zero hv_deg.2
      cases v with
      | r k =>
        simp only [getDegree_r] at ha_zero'
        have hk_zero : k = 0 := Int.natAbs_eq_zero.mp ha_zero'
        simp [hk_zero]
      | sr k =>
        simp only [getDegree_sr] at hb_zero
        have hk_zero : k = 0 := Int.natAbs_eq_zero.mp hb_zero
        simp only [getDegree_sr, hk_zero] at ha_zero'
        norm_num at ha_zero'
    constructor
    · constructor
      · simp
      · rw [hd_zero]
        simp only [getDegree_one, le_refl]
    · intro v hv hv_le
      symm
      exact hv_must_be_one v hv

theorem max_ad_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u) :
  IsMaximalIn
    (if d.a = d.b then s1 * s_alpha_d (d.sub {a := 0, b := 1})
     else if d.b > d.a then s_alpha_d d
     else s0 * s_alpha_d d)
    (Ad u d) := by
  split_ifs with h1 h2
  · exact max_ad_a_eq_b_ends_s0 u d hu h1
  · exact max_ad_b_gt_a_ends_s0 u d hu h2
  · have h3 : d.a > d.b := Nat.lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    exact max_ad_a_gt_b_ends_s0 u d hu h3



/-- Formula (4) candidate when the reduced word for the base point ends in `s0`. -/
def maxAdCandidateEndsS0 (d : Degree) : Vertex :=
  if d.a = d.b then s1 * s_alpha_d (d.sub {a := 0, b := 1})
  else if d.b > d.a then s_alpha_d d
  else s0 * s_alpha_d d

/-- Formula (4), `ends_in_s0` case, using the semantic candidate name. -/
theorem max_ad_candidate_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u) :
    IsMaximalIn (maxAdCandidateEndsS0 d) (Ad u d) := by
  simpa [maxAdCandidateEndsS0] using max_ad_ends_s0 u d hu