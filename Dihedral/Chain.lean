import Dihedral.Degree

open Nat CoxeterSystem DihedralGroup

def IsEdge (u v : Vertex) (α : Root) : Prop :=
  v = u * (s_α α)

notation:50 u " —[" α "]→ " v => IsEdge u v α

theorem edge_exists_iff (u v : Vertex) :
    (∃ α, u —[α]→ v) ↔ ∃ α : Root, v = u * s_α (α) := by
  simp [IsEdge]

inductive HasChain : Vertex → Vertex → Degree → Prop where
  | refl (u : Vertex) : HasChain u u 0
  | step {u v w : Vertex} {d : Degree} {α : Root} :
      HasChain u v d → IsEdge v w α → HasChain u w (d + α.toDegree)

-- 在每一步步进时增加 ℓ w > ℓ v 的判断
inductive HasIncreasingChain : Vertex → Vertex → Degree → Prop where
  | refl (u : Vertex) : HasIncreasingChain u u 0
  | step {u v w : Vertex} {d : Degree} {α : Root} :
      HasIncreasingChain u v d →
      IsEdge v w α →
      (ℓ v < ℓ w) →
      HasIncreasingChain u w (d + α.toDegree)

-- 如果存在任意度数的递增链，则 u < v
def Lt (u v : Vertex) : Prop :=
  ∃ d : Degree, HasIncreasingChain u v d ∧ u ≠ v

lemma chain_length_lt {u v : Vertex} {d : Degree} (h : HasIncreasingChain u v d) :
    ℓ u ≤ ℓ v := by
  induction h with
  | refl => exact le_refl _
  | step _ _ h_lt ih => exact le_of_lt (lt_of_le_of_lt ih h_lt)

lemma chain_length_lt_strict {u v : Vertex} {d : Degree} (h : HasIncreasingChain u v d)
    (hne : u ≠ v) : ℓ u < ℓ v := by
  induction h with
  | refl => contradiction
  | step h_chain h_edge h_lt ih =>
    rename_i v_mid w_final d_mid α
    by_cases heq : u = v_mid
    · subst heq
      exact h_lt
    · have h_u_lt_mid := ih heq
      exact lt_trans h_u_lt_mid h_lt

lemma Lt_trans {u v w} (huv : Lt u v) (hvw : Lt v w) : Lt u w := by
  rcases huv with ⟨d1, huv⟩
  rcases hvw with ⟨d2, hvw⟩
  let rec concat {x y z : Vertex} {d1 d2 : Degree}
      (hc1 : HasIncreasingChain x y d1) (hc2 : HasIncreasingChain y z d2) :
      HasIncreasingChain x z (d1 + d2) := by
    cases hc2 with
    | refl => simp only [add_zero]; exact hc1
    | step hc2_prev edge len_lt =>
      simp only [← add_assoc]
      exact HasIncreasingChain.step (concat hc1 hc2_prev) edge len_lt
  termination_by ℓ z
  use d1 + d2
  constructor
  · exact concat huv.1 hvw.1
  · intro h_eq
    have l1 := chain_length_lt_strict huv.1 huv.2
    have l2 := chain_length_lt_strict hvw.1 hvw.2
    have l3 : ℓ u < ℓ w := lt_trans l1 l2
    rw [h_eq] at l3
    exact lt_irrefl _ l3

lemma Lt_iff_le_not_ge (a b : Vertex) :
    Lt a b ↔ (Lt a b ∨ a = b) ∧ ¬(Lt b a ∨ b = a) := by
  constructor
  · intro h
    constructor
    · left; exact h
    · intro h_ge
      rcases h_ge with (hba | rfl)
      · rcases h with ⟨d1, c1, ne1⟩
        rcases hba with ⟨d2, c2, ne2⟩
        have l1 := chain_length_lt_strict c1 ne1
        have l2 := chain_length_lt_strict c2 ne2
        have contra := lt_trans l1 l2
        exact lt_irrefl _ contra
      · delta Lt at h
        rcases h with ⟨d, chain, ne⟩
        contradiction
  · rintro ⟨(hab | rfl), h_not_ge⟩
    · exact hab
    · exfalso
      apply h_not_ge
      exact Or.inr rfl

instance : PartialOrder D∞ where
  le u v := (Lt u v) ∨ (u = v)
  lt := Lt
  le_refl  u:= Or.inr rfl
  le_trans := by
    rintro a b c (hab|rfl) (hbc|rfl)
    any_goals tauto
    left
    exact Lt_trans hab hbc
  lt_iff_le_not_ge := Lt_iff_le_not_ge
  le_antisymm a b:= by
    rintro (hab|rfl) (hba|h)
    any_goals rfl
    · exfalso
      rcases hab with ⟨d1, c1, ne1⟩
      have l1 := chain_length_lt_strict c1 ne1
      rcases hba with ⟨d2, c2, ne2⟩
      have l2 := chain_length_lt_strict c2 ne2
      have contra := lt_trans l1 l2
      exact lt_irrefl _ contra
    · exact h.symm

lemma exists_root_eq_sr (k : ZMod 0) : ∃ α : Root, s_α α = sr k := by
  let z : ℤ := k.cast
  by_cases h : z > 0
  · -- k > 0, sr k uses alternatingWord 0 1 (2k-1)
    let a := z.natAbs - 1
    let b := z.natAbs
    have h_rel : b = a.succ := by
      dsimp [a, b]
      rw [Nat.sub_add_cancel]
      exact Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr (Int.ne_of_gt h))
    let α : Root := ⟨a, b, Or.inr h_rel⟩
    use α
    dsimp [s_α]
    have : ¬ (α.a > α.b) := by linarith
    simp only [this, ↓reduceIte]
    -- reducedWord(sr k) = alternatingWord 0 1 (2k-1)
    have h_rw : cs.wordProd (reducedWord (sr k)) = sr k := reducedWord_correct (sr k)
    dsimp [reducedWord] at h_rw
    rw [if_pos h] at h_rw
    rw [← h_rw]
    congr
    dsimp [α, a, b]
    omega
  · -- k <= 0, sr k uses alternatingWord 1 0 (2|k|+1)
    let a := z.natAbs + 1
    let b := z.natAbs
    have h_rel : a = b.succ := rfl
    let α : Root := ⟨a, b, Or.inl h_rel⟩
    use α
    dsimp [s_α]
    have : α.a > α.b := by linarith
    simp only [this, ↓reduceIte]
    have h_rw : cs.wordProd (reducedWord (sr k)) = sr k := reducedWord_correct (sr k)
    dsimp [reducedWord] at h_rw
    rw [if_neg (not_lt.mpr (le_of_not_gt h))] at h_rw
    --rw [if_neg (not_lt.mpr (le_of_not_gt h))] at h_rw
    rw [← h_rw]
    congr 2
    dsimp [a, b, α]
    omega

lemma inv_mul_is_sr_of_parity_diff (u v : Vertex)
    (h_parity : (ℓ u) % 2 ≠ (ℓ v) % 2) :
    ∃ k : ℤ, u⁻¹ * v = sr k := by
  -- D∞ 中元素归纳
  let g := u⁻¹ * v
  cases hg : g with
  | sr k => use k
  | r k =>
    exfalso
    have h_len_g : ℓ g % 2 = 0 := by
      rw [hg, length_r]
      simp
    have h_hom : ℓ g % 2 = (ℓ u + ℓ v) % 2 := by
      dsimp [g]
      rw [cs.length_mul_mod_two, cs.length_inv]
    rw [h_hom] at h_len_g
    rw [Nat.add_mod] at h_len_g
    have hu_mod : ℓ u % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    have hv_mod : ℓ v % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    interval_cases ℓ u % 2 <;> interval_cases ℓ v % 2 <;>
    omega

lemma lt_of_succ_length (u v : Vertex) (h : ℓ v = ℓ u + 1) : u < v := by
  -- 确定 u⁻¹v 是反射 sr k
  have h_parity : (ℓ u) % 2 ≠ (ℓ v) % 2 := by
    rw [h, Nat.add_mod]
    match (ℓ u) % 2 with
    | 0 => simp
    | 1 => simp
    | x =>
      simp only [mod_succ]
      by_contra
      cases Nat.mod_two_eq_zero_or_one x with
      | inl hx =>
          have h1 : (x + 1) % 2 = 1 := Nat.succ_mod_two_eq_one_iff.mpr hx
          rw [h1] at this
          rw [this] at hx
          contradiction
      | inr hx =>
          have h1 : (x + 1) % 2 = 0 := Nat.succ_mod_two_eq_zero_iff.mpr hx
          rw [h1] at this
          rw [this] at hx
          contradiction
  obtain ⟨k, hk⟩ := inv_mul_is_sr_of_parity_diff u v h_parity
  obtain ⟨α, hα⟩ := exists_root_eq_sr k
  have h_edge : IsEdge u v α := by
    dsimp [IsEdge]
    rw [hα, ←hk, mul_inv_cancel_left]
  have h_len_lt : ℓ u < ℓ v := by rw [h]; exact Nat.lt_succ_self _
  let chain := HasIncreasingChain.step (HasIncreasingChain.refl u) h_edge h_len_lt
  have h_ne : u ≠ v := by
    intro eq
    rw [eq] at h_len_lt
    exact lt_irrefl _ h_len_lt
  use (0 + α.toDegree)

theorem lt_iff_length_lt (u v : Vertex) :
    u < v ↔ ℓ u < ℓ v := by
  constructor
  · intro h
    rcases h with ⟨d, chain, ne⟩
    exact chain_length_lt_strict chain ne
  · intro h_lt
    let k := ℓ v - ℓ u
    have h_diff : ℓ v = ℓ u + k := (Nat.add_sub_of_le (le_of_lt h_lt)).symm
    generalize hn : k = n
    rw [hn] at h_diff
    induction n generalizing v with
    | zero =>
      rw [Nat.add_zero] at h_diff
      rw [h_diff] at h_lt
      exact absurd h_lt (lt_irrefl _)
    | succ n ih =>
      if hn : n = 0 then
        rw [hn, Nat.add_zero] at h_diff
        exact lt_of_succ_length u v h_diff
       else
      -- 递归情况：长度差 > 1
      have h_len_v_pos : ℓ v > 0 := by
        rw [h_diff]
        have : n + 1 ≥ 1 := Nat.le_add_left 1 n
        omega
      have h_ne_one : v ≠ 1 := by
        intro h
        rw [h, cs.length_one] at h_len_v_pos
        exact lt_irrefl 0 h_len_v_pos
      obtain ⟨i, h_descent⟩ := cs.exists_rightDescent_of_ne_one h_ne_one
      let w := v * cs.simple i
      --∃w，使得 ℓ w + 1 = ℓ v，回到归纳
      have hi : ℓ w = ℓ v - 1 := by
        rw [cs.isRightDescent_iff] at h_descent
        exact Nat.eq_sub_of_add_eq h_descent
      have h_len_w : ℓ w = ℓ v - 1 := hi
      --  u < w
      have h_u_lt_w : ℓ u < ℓ w := by
        rw [h_len_w, h_diff]
        have : n ≥ 1 := Nat.pos_of_ne_zero hn
        omega
      have h_diff_w : ℓ w = ℓ u + n := by
        rw [h_len_w, h_diff]
        simp
      have hk_eq_n : ℓ w - ℓ u = n := by
        rw [h_diff_w]
        simp
      have h_u_le_w : u < w :=ih w h_u_lt_w h_diff_w hk_eq_n
      have h_w_lt_v : w < v := by
        apply lt_of_succ_length
        rw [h_len_w]
        omega
      exact Lt_trans h_u_le_w h_w_lt_v


lemma chain_degree_parity (u v : Vertex) (d : Degree) :
    HasChain u v d →
    ∃ (r s : ℕ), d.a = (φ (u⁻¹ * v)).a + 2 * r ∧
                 d.b = (φ (u⁻¹ * v)).b + 2 * s := by
  intro h
  induction h with
  | refl =>
    use 0, 0
    rw [inv_mul_cancel u, getDegree_one]
    simp only [mul_zero, add_zero]
    exact eq_zero_of_add_eq_zero rfl
  | step h_chain h_edge ih =>
    rename_i v' w d' α
    rcases ih with ⟨r',s', h0', h1'⟩
    let g := u⁻¹ * v'
    let t := s_α α
    have h_gw : u⁻¹ * w = g * t := by
      simp only [IsEdge] at h_edge
      rw [h_edge, mul_assoc]
    obtain ⟨k, m, hk, hm⟩ := degree_add_parity g t
    have h_deg_t : φ t = α.toDegree := φ_s_alpha_eq α
    use r' + k,s' + m
    constructor
    · dsimp [Add.add, Root.toDegree]
      change d'.a + α.a = (φ (u⁻¹ * w)).a + 2 * (r' + k)
      rw [h0', h_gw, show α.a = (α.toDegree).a by rfl]
      rw [← h_deg_t]
      linarith [hk]
    · dsimp [Add.add, Root.toDegree]
      change d'.b + α.b = (φ (u⁻¹ * w)).b + 2 * (s' + m)
      rw [h1', h_gw, show α.b = (α.toDegree).b by rfl]
      simp [← h_deg_t]
      linarith [hm]

-- Compatibility alias for the paper numbering.
lemma lemma_2_5_a (u v : Vertex) (d : Degree) :
    HasChain u v d →
    ∃ (r s : ℕ), d.a = (φ (u⁻¹ * v)).a + 2 * r ∧
                 d.b = (φ (u⁻¹ * v)).b + 2 * s :=
  chain_degree_parity u v d

lemma inv_mul_degree_le_of_chain (u v : Vertex) (d : Degree) (h : HasChain u v d) :
    φ (u⁻¹ * v) ≤ d := by
  obtain ⟨r, s, hr, hs⟩ := chain_degree_parity u v d h
  constructor
  · rw [hr]; exact Nat.le_add_right _ _
  · rw [hs]; exact Nat.le_add_right _ _

-- Compatibility alias for the paper numbering.
lemma lemma_2_5_b (u v : Vertex) (d : Degree) (h : HasChain u v d) :
    φ (u⁻¹ * v) ≤ d :=
  inv_mul_degree_le_of_chain u v d h
