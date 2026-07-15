import Dihedral.Mathlib

open Nat CoxeterSystem DihedralGroup

structure Root where
  a : ℕ
  b : ℕ
  sub_one : (a = b.succ) ∨ (b = a.succ)
deriving DecidableEq

def α0 : Root := ⟨1, 0, Or.inl rfl⟩
def α1 : Root := ⟨0, 1, Or.inr rfl⟩

-- The length of a root is a + b
def Root.length (α : Root) : ℕ := α.a + α.b

notation "Λ" => CoxeterSystem.alternatingWord

@[simp]
lemma length_r (k : ℤ) : ℓ (r k) = 2 * k.natAbs := by
  simp [length_eq, reducedWord, apply_ite List.length, CoxeterSystem.length_alternatingWord]

@[simp]
lemma length_sr (k : ℤ) : ℓ (sr k) = if k > 0 then 2 * k.natAbs - 1 else 2 * k.natAbs + 1 := by
  simp [length_eq, reducedWord, apply_ite List.length, CoxeterSystem.length_alternatingWord]

lemma length_inv_eq (u : D∞) : ℓ u = ℓ u⁻¹ :=
  (cs.length_inv u).symm

-- Compatibility alias for the paper numbering.
lemma lemma_2_1_1 (u : D∞) : ℓ u = ℓ u⁻¹ :=
  length_inv_eq u

lemma length_mul_le (u v : D∞) : ℓ (u * v) ≤ ℓ u + ℓ v :=
  cs.length_mul_le u v

-- Compatibility alias for the paper numbering.
lemma lemma_2_1_3 (u v : D∞) : ℓ (u * v) ≤ ℓ u + ℓ v :=
  length_mul_le u v

def Di_induction_on {P : D∞ → Prop} (g : D∞)
    (r : ∀ k, P (r k)) (sr : ∀ k, P (sr k)) : P g := by
  cases g
  · apply r
  · apply sr

theorem length_mul_eq_add_or_sub (u v : D∞) (huv : ℓ u ≤ ℓ v) :
    ℓ (u * v) = ℓ u + ℓ v ∨ ℓ (u * v) = ℓ v - ℓ u := by
  cases u <;> cases v <;>
    simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, length_r, length_sr] at huv ⊢ <;>
    (try split_ifs at huv ⊢) <;> omega

structure Degree where
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr

instance : Add Degree where
  add d e := ⟨d.a + e.a, d.b + e.b⟩

instance : Zero Degree where
  zero := ⟨0, 0⟩

def Degree.scale (n : ℕ) (d : Degree) : Degree :=
  ⟨n * d.a, n * d.b⟩

instance : HMul ℕ Degree Degree where
  hMul := Degree.scale

def Degree.sub (b d2 : Degree) : Degree :=
  ⟨b.a - d2.a, b.b - d2.b⟩

@[ext]
theorem Degree.ext {d1 d2 : Degree} (h0 : d1.a = d2.a) (h1 : d1.b = d2.b) : d1 = d2 := by
  cases d1; cases d2
  simp only at h0 h1
  rw [h0, h1]

@[simp]
instance : AddCommMonoid Degree where
  add := (· + ·)
  zero := 0
  add_assoc a b c := by
    ext <;> apply Nat.add_assoc
  zero_add a := by
    ext <;> apply Nat.zero_add
  add_zero a := by
    ext <;> apply Nat.add_zero
  add_comm a b := by
    ext <;> apply Nat.add_comm
  nsmul := fun n d => ⟨n * d.a, n * d.b⟩
  nsmul_zero n := by
    ext <;> (simp; rfl)
  nsmul_succ n d := by
    ext; all_goals
      simp only [succ_mul]; rfl

-- Partial order on degrees
instance : PartialOrder Degree where
  le d1 d2 := d1.a ≤ d2.a ∧ d1.b ≤ d2.b
  le_refl d := ⟨le_refl _, le_refl _⟩
  le_trans d1 d2 d3 h12 h23 := ⟨le_trans h12.1 h23.1, le_trans h12.2 h23.2⟩
  le_antisymm d1 d2 h12 h21 := by
    cases d1; cases d2
    simp only [Degree.mk.injEq] at *
    exact ⟨Nat.le_antisymm h12.1 h21.1, Nat.le_antisymm h12.2 h21.2⟩

@[simp]
lemma Degreele_le_def (d1 d2 : Degree) : d1 ≤ d2 ↔ d1.a ≤ d2.a ∧ d1.b ≤ d2.b := Iff.rfl

def getDegree : D∞ → Degree
  | .r i =>
    let k := (i.cast : ℤ).natAbs
    ⟨k, k⟩
  | .sr i =>
    let k : ℤ := i.cast
    if k ≥ 0 then
      if i = 0 then ⟨1, 0⟩ else ⟨k.natAbs - 1, k.natAbs⟩
    else
      ⟨k.natAbs + 1, k.natAbs⟩

private lemma getDegree_sr_eq (k : ZMod 0) : -- (extracted by Fuse golfer)
    getDegree (sr k) = ⟨((k.cast : ℤ) - 1).natAbs, (k.cast : ℤ).natAbs⟩ := by
  dsimp [getDegree]
  split_ifs with h h'
  · if h0 : k = 0 then
      simp [h0]
    else
      simp [h']
  · congr
    have hk_ne : (k.cast : ℤ) ≠ 0 := fun hk0 => h' (by exact_mod_cast hk0)
    omega
  · congr
    omega

@[simp]
lemma getDegree_one : getDegree (1 : D∞) = ⟨0, 0⟩ := rfl

def Root.toDegree (α : Root) : Degree :=⟨α.a, α.b⟩

-- Vertices. In the case of D∞, vertices are group elements
abbrev Vertex := D∞

lemma getDegree_alternating_0_even (k : ℕ) :
    getDegree (cs.wordProd (alternatingWord 0 1 (2 * k))) = ⟨k, k⟩ := by
  rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * k)]
  simp only [even_two, Even.mul_right, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
    sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, r_pow, one_mul]
  simp [getDegree]

lemma getDegree_alternating_1_even (k : ℕ) :
    getDegree (cs.wordProd (alternatingWord 1 0 (2 * k))) = ⟨k, k⟩ := by
  rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * k)]
  simp only [even_two, Even.mul_right, ↓reduceIte, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr,
    zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, r_pow, neg_mul,
    one_mul]
  simp [getDegree]

lemma getDegree_alternatin_even {s} (k : ℕ) :
    getDegree (cs.wordProd (alternatingWord s (1-s) (2 * k))) = ⟨k, k⟩  := by
  fin_cases s <;>
  simp only [Fin.zero_eta, Fin.isValue, sub_zero]
  · exact getDegree_alternating_0_even k
  · exact getDegree_alternating_1_even k

lemma getDegree_alternating_0_odd (k : ℕ) :
    getDegree (cs.wordProd (alternatingWord 0 1 (2 * k + 1))) = ⟨k, k + 1⟩ := by
  rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * k + 1)]
  simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr, sub_zero,
    r_pow, one_mul, sr_mul_r]
  rw [show (2 * k + 1) / 2 = k from by omega, getDegree_sr_eq]
  simp only [zmod0_cast_add_int, zmod0_cast_one_int, zmod0_cast_natCast_int, Degree.mk.injEq]
  omega

lemma getDegree_alternating_1_odd (k : ℕ) :
    getDegree (cs.wordProd (alternatingWord 1 0 (2 * k + 1))) = ⟨k+1, k⟩ := by
  rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * k + 1)]
  simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr, zero_sub,
    r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
  rw [show (2 * k + 1) / 2 = k from by omega, getDegree_sr_eq]
  simp only [zmod0_cast_neg_int, zmod0_cast_natCast_int, Degree.mk.injEq]
  omega


def s_α (α : Root) : D∞ :=
  if α.a > α.b then
    cs.wordProd (Λ  1 0 (α.a + α.b))
  else
    cs.wordProd (Λ 0 1 (α.a + α.b))

@[simp]
lemma s_alpha_alpha0 : s_α α0 = s0 := by
  simp only [s_α, α0, gt_iff_lt, zero_lt_one, ↓reduceIte, Fin.isValue, add_zero, alternatingWord,
    List.concat_eq_append, List.nil_append, cs.wordProd_singleton, ← s0', s0]

@[simp]
lemma s_alpha_alpha1 : s_α α1 = s1 := by
  simp only [s_α, α1, gt_iff_lt, Fin.isValue, zero_add, alternatingWord,
    List.concat_eq_append, List.nil_append, cs.wordProd_singleton, ← s1', s1]
  norm_num

theorem length_root_reflection (α : Root) :
    ℓ (s_α α) = α.a + α.b := by
  rw [s_α]
  split_ifs with h
  <;>
  simp [length_eq, alternating_reducedWord]

-- Notation φ for the degree map getDegree
notation "φ" => getDegree

lemma φ_s_alpha_eq (α : Root) : φ (s_α α) = α.toDegree := by
  simp only [s_α, gt_iff_lt, Root.toDegree]
  split_ifs with h_gt
  · rcases α.sub_one with h | h
    · rw [h]
      rw [show α.b.succ + α.b = 2 * α.b + 1 by omega]
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul]
        using getDegree_alternating_1_odd α.b
    · omega
  · rcases α.sub_one with h | h
    · omega
    · rw [h]
      rw [show α.a + (α.a + 1) = 2 * α.a + 1 by omega]
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul]
        using getDegree_alternating_0_odd α.a

@[simp]
lemma getDegree_r (k : ZMod 0) :
    φ (r k) = ⟨(k.cast : ℤ).natAbs, (k.cast : ℤ).natAbs⟩ := rfl

lemma getDegree_r_neg_natCast (a : ℕ) : φ (r (-(a : ℤ))) = ⟨a, a⟩ := by
  ext <;> simp [getDegree_r]

lemma getDegree_sr (k : ZMod 0) :
    φ (sr k) = ⟨((k.cast : ℤ) - 1).natAbs, (k.cast : ℤ).natAbs⟩ :=
  getDegree_sr_eq k

-- Parity of degree addition
lemma degree_add_parity (g h : D∞) :
    ∃ (r s : ℕ), (φ g).a + (φ h).a = (φ (g * h)).a + 2 * r
               ∧ (φ g).b + (φ h).b = (φ (g * h)).b + 2 * s := by
  cases g with
  | r y =>
    cases h with
    | r x =>
      rcases natAbs_add_eq_natAbs_add_two_mul (y.cast : ℤ) (x.cast : ℤ) with ⟨r, hr⟩
      simp only [getDegree_r, r_mul_r, zmod0_cast_add_int]
      exact ⟨r, r, by omega, by omega⟩
    | sr x =>
      rcases natAbs_sub_eq_natAbs_add_two_mul ((x.cast : ℤ) - 1) (y.cast : ℤ) with ⟨r, hr⟩
      rcases natAbs_sub_eq_natAbs_add_two_mul (x.cast : ℤ) (y.cast : ℤ) with ⟨s, hs⟩
      simp only [getDegree_r, getDegree_sr, r_mul_sr, zmod0_cast_sub_int]
      exact ⟨r, s, by omega, by omega⟩
  | sr y =>
    cases h with
    | r x =>
      rcases natAbs_add_eq_natAbs_add_two_mul ((y.cast : ℤ) - 1) (x.cast : ℤ) with ⟨r, hr⟩
      rcases natAbs_add_eq_natAbs_add_two_mul (y.cast : ℤ) (x.cast : ℤ) with ⟨s, hs⟩
      simp only [getDegree_sr, getDegree_r, sr_mul_r, zmod0_cast_add_int]
      exact ⟨r, s, by omega, by omega⟩
    | sr x =>
      rcases natAbs_sub_eq_natAbs_add_two_mul ((x.cast : ℤ) - 1) ((y.cast : ℤ) - 1) with ⟨r, hr⟩
      rcases natAbs_sub_eq_natAbs_add_two_mul (x.cast : ℤ) (y.cast : ℤ) with ⟨s, hs⟩
      simp only [getDegree_sr, sr_mul_sr, getDegree_r, zmod0_cast_sub_int]
      exact ⟨r, s, by omega, by omega⟩


