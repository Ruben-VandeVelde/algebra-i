import data.fintype.basic
import data.nat.totient
import data.zmod.quotient
import field_theory.finite.basic
import group_theory.perm.cycle.concrete
import group_theory.subgroup.basic
import linear_algebra.general_linear_group
import ring_theory.int.basic

open_locale nat

/-!
§1. Groups
§1.2 Subgroups and Lagrange's Theorem
-/

def l1_2_2_ba {G : Type*} [group G] (H : subgroup G) : group H := infer_instance

lemma l1_2_2_ba' {G : Type*} [group G] (H : subgroup G) :
  (∀ a b : H, ((a * b : H) : G) = (a * b : G)) ∧ (((1 : H) : G) = 1) :=
begin
  refine ⟨_, subgroup.coe_one _⟩,
  rintro ⟨a, ha⟩ ⟨b, hb⟩,
  rw [mul_mem_class.mk_mul_mk, subgroup.coe_mk, subgroup.coe_mk, subgroup.coe_mk, mul_left_inj],
end

def l1_2_2_ab {G : Type*} [group G] (H : set G) [group H]
  (hmul : ∀ a b : H, ((a * b : H) : G) = (a * b : G)) (h1 : ((1 : H) : G) = 1) :
  subgroup G := {
  carrier := H,
  mul_mem' := λ a b ha hb, by {
    convert subtype.mem (⟨a, ha⟩ * ⟨b, hb⟩),
    simp [hmul] },
  one_mem' := by {
    convert subtype.mem 1,
    exact h1.symm },
  inv_mem' := λ x hx, by {
    rw ←(subtype.coe_mk x hx),
    convert subtype.mem ⟨x, hx⟩⁻¹,
    rw [inv_eq_iff_mul_eq_one, ←hmul, mul_right_inv, h1] } }

lemma l1_2_2_bc {G : Type*} [group G] (H : subgroup G) :
  (H : set G).nonempty ∧ ∀ h₁ h₂, h₁ ∈ (H : set G) → h₂ ∈ (H : set G) → h₁ * h₂⁻¹ ∈ (H : set G) :=
begin
  refine ⟨⟨1, set_like.mem_coe.mpr (one_mem _)⟩, λ h₁ h₂ h₁mem h₂mem, _⟩,
  rw [set_like.mem_coe] at h₁mem h₂mem ⊢,
  exact subgroup.mul_mem _ h₁mem (subgroup.inv_mem _ h₂mem)
end

def l1_2_2_cb {G : Type*} [group G] (H : set G) (hne : H.nonempty)
  (hmem : ∀ {h₁ h₂}, h₁ ∈ H → h₂ ∈ H → h₁ * h₂⁻¹ ∈ H) :
  subgroup G :=
have h1 : (1 : G) ∈ H,
{ obtain ⟨x, hx⟩ := hne,
  have h1 := hmem hx hx,
  rwa mul_right_inv at h1 },
have hinv : ∀ {h}, h ∈ H → h⁻¹ ∈ H,
{ intros h hh,
  convert hmem h1 hh,
  rw one_mul },
{ carrier := H,
  mul_mem' := λ a b ha hb, by {
    convert hmem ha (hinv hb),
    rw inv_inv },
  one_mem' := h1,
  inv_mem' := λ x, hinv }

def ex_1_2_3_1 {G : Type*} [group G] : subgroup G :=
{ carrier := {1},
  mul_mem' := λ a b ha hb, by {
    rw set.mem_singleton_iff at ha hb ⊢,
    rw [ha, hb, one_mul] },
  one_mem' := set.mem_singleton _,
  inv_mem' := λ a ha, by {
    rw set.mem_singleton_iff at ha ⊢,
    rw [ha, inv_one] } }

def ex_1_2_3_2 (n : ℤ) : add_subgroup ℤ :=
add_subgroup.zmultiples n
lemma l1_2_3_2 (n : ℤ) : (ex_1_2_3_2 n : set ℤ) = { k : ℤ | n ∣ k } :=
begin
  ext,
  simp [ex_1_2_3_2, int.mem_zmultiples_iff],
end

def ex_1_2_3_3 (K : Type*) [field K] (n : ℕ) : subgroup (matrix.general_linear_group (fin n) K) :=
{ carrier := { A | matrix.det A = 1 },
  mul_mem' := λ a b ha hb, by {
    rw [set.mem_set_of, matrix.general_linear_group.coe_fn_eq_coe] at ha hb ⊢,
    rw [matrix.general_linear_group.coe_mul, matrix.det_mul, ha, hb, one_mul] },
  one_mem' := by {
    rw [set.mem_set_of, matrix.general_linear_group.coe_fn_eq_coe,
      matrix.general_linear_group.coe_one, matrix.det_one] },
  inv_mem' := λ a ha, by {
    rw [set.mem_set_of, matrix.general_linear_group.coe_fn_eq_coe] at ha ⊢,
    rw [matrix.coe_units_inv, matrix.det_nonsing_inv, ring.inverse_eq_inv', ha, inv_one] } }

def l1_2_4 {G : Type*} [group G] (S : set $ subgroup G) : subgroup G := Inf S
lemma l1_2_4' {G : Type*} [group G] (S : set $ subgroup G) :
  ((l1_2_4 S) : set G) = ⋂ s ∈ S, (s : set G) := subgroup.coe_Inf _

def d1_2_5 {G : Type*} [group G] (X : set G) : subgroup G := subgroup.closure X
lemma l1_2_5' {G : Type*} [group G] (X : set G) :
  (subgroup.closure X : set G) = ⋂ H' ∈ {H : subgroup G | X ⊆ H}, (H' : set G) := rfl

def n1_2_5_set  {G : Type*} [group G] (X : set G) :
  set (list G) := { m : list G | ∀ x ∈ m, x ∈ X ∪ X⁻¹ }

def n1_2_5 {G : Type*} [group G] (X : set G) : subgroup G :=
{ carrier := { (list.prod x) | x ∈ n1_2_5_set X },
  mul_mem' := begin
    intros a b ha hb,
    simp [set.mem_set_of] at ha hb ⊢,
    obtain ⟨xa, hxa⟩ := ha,
    obtain ⟨xb, hxb⟩ := hb,
    refine ⟨xa ++ xb, _, _⟩,
    { simp only [n1_2_5_set, set.mem_set_of] at hxa hxb ⊢,
      intros x hx,
      obtain hx'|hx' := list.mem_append.mp hx,
      exacts [hxa.1 x hx', hxb.1 x hx'] },
    { rw [list.prod_append, hxa.2, hxb.2] }
  end,
  one_mem' := begin
    simp [set.mem_set_of],
    refine ⟨[], _, list.prod_nil⟩,
    simp [n1_2_5_set, set.mem_set_of]
  end,
  inv_mem' := begin
    intros a ha,
    simp [set.mem_set_of] at ha ⊢,
    obtain ⟨xa, hxa⟩ := ha,
    refine ⟨(xa.map has_inv.inv).reverse, _, _⟩,
    { simpa [n1_2_5_set, set.mem_set_of, or_comm] using hxa.1 },
    { rw [←hxa.2, list.prod_inv_reverse] }
  end }

-- 2019-2020
lemma n1_2_5' {G : Type*} [group G] (X : set G) :
  (subgroup.closure X : set G) = { (list.prod x) | x ∈ n1_2_5_set X } :=
begin
  simp only [subgroup.closure, subgroup.coe_Inf],
  apply subset_antisymm,
  { intros x hx,
    simp only [set.mem_Inter] at hx,
    simp only [set.mem_set_of],
    specialize hx (n1_2_5 X) _,
    { intros y hy,
      simp only [n1_2_5, set.mem_set_of, subgroup.coe_set_mk],
      refine ⟨[y], _, list.prod_singleton⟩,
      simp only [hy, n1_2_5_set, forall_eq, true_or, set.mem_set_of, list.mem_singleton, set.mem_union] },
    simpa [n1_2_5] using hx },
  { intros x hx,
    simp only [set.mem_set_of, n1_2_5_set] at hx,
    simp only [set.mem_Inter, set_like.mem_coe],
    intros i hi,
    obtain ⟨y, h1, rfl⟩ := hx,
    induction y,
    { simp only [list.prod_nil, one_mem], },
    { simp only [list.prod_cons],
      apply mul_mem,
      { specialize h1 y_hd (list.mem_cons_self _ _),
        obtain h1|h1 := (set.mem_union _ _ _).mp h1,
        { exact hi h1 },
        { rw ←inv_inv y_hd, exact subgroup.inv_mem _ (hi h1) } },
      { exact y_ih (λ y hy, h1 _ (list.mem_cons_of_mem _ hy)) } } },
end

def l1_2_8_a {G : Type*} [group G] (H : subgroup G) : setoid G :=
quotient_group.left_rel H
lemma l1_2_8_b {G : Type*} [group G] [fintype G] (H : subgroup G) [fintype H] :
  fintype.card H ∣ fintype.card G :=
subgroup.card_subgroup_dvd_card H

open_locale cardinal
lemma l1_2_9 {G : Type*} [group G] (H : subgroup G) :
  #(quotient (quotient_group.right_rel H)) = #(quotient (quotient_group.left_rel H))  :=
cardinal.mk_congr $ quotient_group.quotient_right_rel_equiv_quotient_left_rel H

def d1_2_10 {G : Type*} [group G] (H : subgroup G) := #(G ⧸ H)
lemma d1_2_10' {G : Type*} [group G] [fintype G] (H : subgroup G) :
  nat.card (G ⧸ H) = nat.card G / nat.card H :=
begin
  haveI : fintype H,
  { classical, apply_instance },
  have : 0 < nat.card H,
  { rw [nat.card_eq_fintype_card, fintype.card_pos_iff],
    exact ⟨⟨1, one_mem _⟩⟩ },
  rw [←subgroup.card_mul_index H, nat.mul_div_cancel_left _ this, subgroup.index],
end

open_locale coset

lemma xmp_1_2_11 (n : ℕ+) : add_subgroup.index (ex_1_2_3_2 n) = n :=
begin
  simp [ex_1_2_3_2, add_subgroup.index,
    nat.card_congr (int.quotient_zmultiples_nat_equiv_zmod n).to_equiv, nat.card_eq_fintype_card,
    zmod.card],
end

lemma n_1_2_13 {G : Type*} [group G] (A B : set G) (g : G) :
  A = { (g * b) | b ∈ B } ↔ { (g⁻¹ * a) | a ∈ A } = B :=
begin
  split; { rintro rfl, ext, simp },
end

def ex_1_2_4' {G : Type*} [group G] (x : G × G) := x.1 * x.2
lemma ex_1_2_4 {G : Type*} [group G] (A B : set G) :
  #({ (ex_1_2_4' x) | x ∈ A ×ˢ B} : set G) ≤ #A * #B :=
begin
  simp only [ex_1_2_4', set.mem_prod, exists_prop, prod.exists],
  calc # ↥{x | ∃ (a b : G), (a ∈ A ∧ b ∈ B) ∧ a * b = x}
      = # ↥⋃ (a ∈ A) (b ∈ B), ({ (a : G) * (b : G) } : set G) : _
  ... = # ↥⋃ (a : A) (b : B), ({ (a : G) * (b : G) } : set G) : _
  ... ≤ cardinal.sum (λ (a : A), cardinal.sum $ λ (b : B), # ({ (a : G) * (b : G) } : set G)) : _
  ... = # ↥A * # ↥B : _,
  { congr' 2,
    ext x,
    simp [set.set_of_exists, set.set_of_and, ←exists_and_distrib_left, and_assoc] },
  { simp only [set.Union_coe_set],
    congr },
  { exact cardinal.mk_Union_le_sum_mk.trans
      (cardinal.sum_le_sum _ _ (λ a, cardinal.mk_Union_le_sum_mk)) },
  { simp_rw [cardinal.mk_singleton, cardinal.sum_const', mul_one] },
end

lemma ex_1_2_5 {G : Type*} [group G] (A B : set G) (g : G) :
  { (g * x) | x ∈ A ∩ B } = { (g * x) | x ∈ A } ∩ { (g * x) | x ∈ B } :=
begin
  ext y, simp only [set.mem_inter_eq, set.mem_set_of_eq, exists_prop],
  split,
  { rintro ⟨x, ⟨ha, hb⟩, hx⟩,
    exact ⟨⟨x, ha, hx⟩, ⟨x, hb, hx⟩⟩ },
  { rintro ⟨⟨x, ha, hx⟩, ⟨x', hb, hx'⟩⟩,
    obtain rfl : x = x',
    { rw [←mul_right_inj g, hx, hx'] },
    exact ⟨x, ⟨ha, hb⟩, hx⟩ }
end

lemma ex_1_2_6 {G : Type*} [fintype G] [group G] (A B : subgroup G) (h : A ≤ B) :
  subgroup.index A = subgroup.relindex A B * subgroup.index B :=
(subgroup.relindex_mul_index h).symm

lemma ex_1_2_7 {G : Type*} [group G] (A B : subgroup G) (h : A ≤ B) :
  subgroup.index A = subgroup.relindex A B * subgroup.index B :=
(subgroup.relindex_mul_index h).symm

def d1_2_14 (G : Type*) [group G] (g : G) (n : ℤ) := g ^ n

lemma l1_2_15_i (G : Type*) [group G] (g : G) (m n : ℤ) :
  g ^ (m + n) = g ^ m * g ^ n := zpow_add g m n
lemma l1_2_15_i' (G : Type*) [group G] (g : G) (m n : ℤ) :
  (g ^ m) ^ n = g ^ (m * n) := (zpow_mul g m n).symm
lemma l1_2_15_ii (G : Type*) [group G] (g : G) (m n : ℤ) :
  (subgroup.closure ({g} : set G) : set G) = { (g ^ k) | k : ℤ } :=
begin
  ext,
  simp only [set_like.mem_coe, set.mem_set_of_eq, subgroup.mem_closure_singleton],
end

lemma l1_2_17 (G : Type*) [group G] (g a b : G) (m n : ℤ)
  (ha : a ∈ subgroup.closure ({g} : set G)) (hb : b ∈ subgroup.closure ({g} : set G)) :
  a * b = b * a :=
begin
  rw subgroup.mem_closure_singleton at ha hb,
  obtain ⟨n, rfl⟩ := ha,
  obtain ⟨m, rfl⟩ := hb,
  rw [←zpow_add, ←zpow_add, add_comm],
end

lemma l1_2_19 (G : Type*) [group G] (g : G) (d : ℤ) :
  g ^ d = 1 ↔ (order_of g : ℤ) ∣ d :=
order_of_dvd_iff_zpow_eq_one.symm

lemma zpow_eq_zpow_iff_modeq (G : Type*) [group G] (x : G) (m n : ℤ) :
  x ^ n = x ^ m ↔ n ≡ m [ZMOD (order_of x)] :=
begin
  wlog hmn : m ≤ n,
  obtain ⟨k, hk⟩ := int.eq_coe_of_zero_le (sub_nonneg_of_le hmn),
  calc x ^ n = x ^ m
      ↔ x ^ (k : ℤ) = 1 : _
  ... ↔ x ^ k = 1 : _
  ... ↔ _ : _,
  { simp [←hk, zpow_sub, mul_inv_eq_one] },
  { rw zpow_coe_nat },
  { rw [pow_eq_one_iff_modeq, nat.modeq_zero_iff_dvd, ←int.coe_nat_dvd, ←hk,
      ←zmod.int_coe_eq_int_coe_iff_dvd_sub, eq_comm, zmod.int_coe_eq_int_coe_iff] }
end

lemma l1_2_20_i (G : Type*) [group G] (g : G) (i j : ℤ) (h : is_of_fin_order g) :
  g ^ i = g ^ j ↔ i ≡ j [ZMOD (order_of g)] :=
zpow_eq_zpow_iff_modeq G g j i

namespace subgroup
lemma mem_closure_singleton' {G : Type*} [group G]
  {x y : G} (h : is_of_fin_order x) : y ∈ closure ({x} : set G) ↔ ∃ n < order_of x, x ^ n = y :=
begin
  simp only [←zpowers_eq_closure, exists_prop],
--  rw mem_zpowers_iff_mem_range_order_of,
  split; rintro ⟨i, hi⟩,
  { suffices : ∃ (n : ℤ), 0 ≤ n ∧ n < order_of x ∧ x ^ n = y,
    { obtain ⟨n, hnonneg, hlt, heq⟩ := this,
      refine ⟨n.nat_abs, _, _⟩,
      { rwa [←int.coe_nat_lt, int.nat_abs_of_nonneg hnonneg] },
      { rwa [←zpow_coe_nat, int.nat_abs_of_nonneg hnonneg] } },
    have ho : 0 < (order_of x : ℤ),
    { rwa [int.coe_nat_pos, pos_iff_ne_zero, ne.def, order_of_eq_zero_iff, not_not] },
    refine ⟨i % order_of x, int.mod_nonneg _ ho.ne', int.mod_lt_of_pos _ ho, _⟩,
    rw [←hi, l1_2_20_i _ _ _ _ h],
    exact int.mod_modeq _ _ },
  { use i,
    simp only [zpow_coe_nat, hi.2], }
end
end subgroup

lemma l1_2_20_i' (G : Type*) [group G] (g : G) (h : is_of_fin_order g) :
  (subgroup.closure ({g} : set G) : set G) = { (g ^ i) | i ∈ set.Ico 0 (order_of g) } :=
begin
  ext, simp [subgroup.mem_closure_singleton' h],
end

@[simp] lemma int.modeq_zero_iff {a b : ℤ} : a ≡ b [ZMOD 0] ↔ a = b :=
by rw [int.modeq, int.mod_zero, int.mod_zero]

lemma l1_2_20_ii (G : Type*) [group G] (g : G) (i j : ℤ) (h : ¬is_of_fin_order g) :
  g ^ i = g ^ j ↔ i = j :=
begin
  rw ←order_of_eq_zero_iff at h,
  rw [zpow_eq_zpow_iff_modeq, h, int.coe_nat_zero, int.modeq_zero_iff],
end

lemma l1_2_20_ii' (G : Type*) [group G] (g : G) (h : ¬is_of_fin_order g) :
  (subgroup.closure ({g} : set G) : set G) = { (g ^ i) | i : ℤ } :=
begin
  rw ←subgroup.zpowers_eq_closure,
  ext, simp [subgroup.mem_zpowers_iff],
end

lemma l1_2_20_iii (G : Type*) [group G] (g : G) (h : is_of_fin_order g) :
  #(subgroup.closure ({g} : set G) : set G) = order_of g :=
begin
  classical,
  have := (order_of_pos' h).ne',
  rw [l1_2_20_i' _ _ h],
  transitivity #((set.Ico 0 (order_of g)).image (λ i, g ^ i)),
  { congr' 2, apply set.ext (λ x, _), simp, },
  simp only [cardinal.mk_fintype, nat.cast_inj, fintype.card_of_finset],
  rw finset.card_image_of_inj_on,
  simp only [tsub_zero, eq_self_iff_true, set.to_finset_card, nat.card_fintype_Ico],
  intros x hx y hy hxy,
  rwa [pow_eq_pow_iff_modeq, nat.modeq, nat.mod_eq_of_lt, nat.mod_eq_of_lt] at hxy,
  simpa using hy,
  simpa using hx,
end

section
universes u v

variables {G : Type u} {A : Type v}
variables {x y : G} {a b : A} {n m : ℕ}
variables [group G] [add_group A] {x a} {i : ℤ}

lemma zpow_inj_iff_of_order_of_eq_zero (h : order_of x = 0) {n m : ℤ} :
  x ^ n = x ^ m ↔ n = m :=
begin
  rw order_of_eq_zero_iff at h,
  exact l1_2_20_ii _ _ n m h,
end
end

lemma l1_2_20_iii' (G : Type*) [group G] (g : G) (h : ¬is_of_fin_order g) :
  set.infinite (subgroup.closure ({g} : set G) : set G) :=
begin
  rw [l1_2_20_ii' _ _ h],
  rw ←order_of_eq_zero_iff at h,
  have : ((set.univ : set ℕ).image (λ i, g ^ i)).infinite,
  { simp,
    apply set.infinite_range_of_injective,
    intros x y hxy,
    rwa pow_inj_iff_of_order_of_eq_zero h at hxy, },
  apply set.infinite.mono _ this,
  intros x hx,
  simp at hx,
  simp,
  obtain ⟨n, hn⟩ := hx,
  use n,
  simp only [zpow_coe_nat, hn],
end

lemma l1_2_21 (G : Type*) [group G] [fintype G] (g : G) : order_of g ∣ fintype.card G :=
order_of_dvd_card_univ

lemma l1_2_21' (G : Type*) [group G] [fintype G] (g : G) : g ^ (fintype.card G) = 1 :=
order_of_dvd_iff_pow_eq_one.mp order_of_dvd_card_univ

namespace int
theorem gcd_val (a b : ℤ) : gcd a b = gcd (b % a) a :=
begin
  rw [←nat_abs_euclidean_domain_gcd, euclidean_domain.gcd_val, nat_abs_euclidean_domain_gcd],
end
end int

lemma coe_mul_inv_eq_one''  {n : ℕ} (x : int) (h : is_coprime x n) :
  (x * x⁻¹ : zmod n) = 1 :=
begin
  cases n,
  { simp [is_coprime_zero_right, -is_coprime] at h,
    rw [zmod.mul_inv_eq_gcd, nat.gcd_zero_right, nat.cast_eq_one, zmod.val, int.cast_id,
      int.is_unit.nat_abs_eq h] },
  { haveI := n.succ_pos,
    rw [←int.gcd_eq_one_iff_coprime, int.gcd_comm, int.gcd_val] at h,
    rw [zmod.mul_inv_eq_gcd, ←int.coe_nat_gcd, zmod.val_int_cast, h, nat.cast_one] },
end

def unit_of_is_coprime' {n : ℕ} (x : ℤ) (h : is_coprime x n) : (zmod n)ˣ :=
⟨x, x⁻¹, coe_mul_inv_eq_one'' x h, by rw [mul_comm, coe_mul_inv_eq_one'' x h]⟩

@[simp] lemma coe_unit_of_is_coprime {n : ℕ} (x : ℤ) (h : is_coprime x n) :
  (unit_of_is_coprime' x h : zmod n) = x := rfl

@[simp] lemma zmod.pow_totient' {n : ℕ} (x : (zmod n)ˣ) : x ^ nat.totient n = 1 :=
begin
  cases n,
  { simp },
  apply zmod.pow_totient,
end

lemma l1_2_23 (n : ℕ+) (x : ℤ) (h : is_coprime x n) : x ^ nat.totient n ≡ 1 [ZMOD n] :=
by rw [coe_coe n, ←eq_iff_modeq_int (zmod n), int.cast_pow, int.cast_one,
    ←coe_unit_of_is_coprime _ h, ←units.coe_pow, units.coe_eq_one, ←zmod.pow_totient' _]

noncomputable def d1_2_24 (G : Type*) [group G] : ℕ := monoid.exponent G

lemma d1_2_24_dvd {G : Type*} [group G] (g : G) : order_of g ∣ d1_2_24 G :=
monoid.order_dvd_exponent g

lemma d1_2_24_dvd' {G : Type*} [group G] (n : ℕ) (h : ∀ g : G, order_of g ∣ n) :
  d1_2_24 G ∣ n :=
monoid.exponent_dvd_of_forall_pow_eq_one G n $ forall_imp (λ g, order_of_dvd_iff_pow_eq_one.mp) h

lemma commute_of_order_dvd_two {G : Type*} [group G] {a b : G} (h : ∀ g : G, order_of g ∣ 2) :
  a * b = b * a :=
begin
  simp_rw order_of_dvd_iff_pow_eq_one at h,
  rw [←mul_right_inj a, ←mul_left_inj b],
  calc a * (a * b) * b
      = a ^ 2 * b ^ 2 : by group
  ... = 1 : by rw [h, h, mul_one]
  ... = (a * b) ^ 2 : by rw [h]
  ... = a * (b * a) * b : by { simp only [sq], group },

end

example {G : Type*} [group G] (h : monoid.exponent G = 2) (a b : G) : a * b = b * a :=
commute_of_order_dvd_two (λ g, h ▸ monoid.order_dvd_exponent g)

-- Lemmas due to Yakov Pechersky.
namespace rat

@[simp] lemma coe_int_inv_num (x : ℤ) : (x : ℚ)⁻¹.num = int.sign x :=
by simp [inv_def', div_num_denom, num_mk]

@[simp] lemma coe_int_inv_denom (x : ℤ) : (x : ℚ)⁻¹.denom = if x = 0 then 1 else x.nat_abs :=
by simp [inv_def', div_num_denom, denom_mk]

end rat

lemma n1_2_24 : ∃ {G : Type} [add_group G],
  by exactI (∀ g : G, is_of_fin_add_order g) ∧ add_monoid.exponent G = 0 :=
begin
  refine ⟨ℚ ⧸ (add_subgroup.zmultiples (1 : ℚ)), infer_instance, λ g, _, _⟩,
  { induction g using quotient_add_group.induction_on',
    rw is_of_fin_add_order_iff_nsmul_eq_zero,
    refine ⟨g.denom, g.pos, _⟩,
    rw [←quotient_add_group.coe_nsmul, nsmul_eq_mul, quotient_add_group.eq_zero_iff,
      add_subgroup.mem_zmultiples_iff],
    use g.num,
    rw [int.smul_one_eq_coe, ←rat.mul_denom_eq_num, mul_comm] },
  { rw [add_monoid.exponent_eq_zero_iff, add_monoid.exponent_exists],
    push_neg,
    refine λ n hn, ⟨(1 / (2 * n) : ℚ), _⟩,
    rw [←quotient_add_group.coe_nsmul, nsmul_eq_mul, ne.def, quotient_add_group.eq_zero_iff,
      add_subgroup.mem_zmultiples_iff, not_exists],
    refine λ x, ne_of_apply_ne rat.denom _,
    rw [int.smul_one_eq_coe, rat.coe_int_denom, one_div, mul_inv_rev, ←mul_assoc,
      mul_inv_cancel ((@nat.cast_ne_zero ℚ _ _ _).mpr hn.ne'), one_mul, ←int.cast_two,
      rat.coe_int_inv_denom],
    norm_num },
end

lemma n1_2_24' {G : Type*} [group G] [fintype G] : d1_2_24 G ≠ 0 :=
monoid.exponent_ne_zero_of_fintype

lemma l1_2_25 {G : Type*} [group G] [fintype G] : d1_2_24 G ∣ fintype.card G :=
monoid.exponent_dvd_of_forall_pow_eq_one G (fintype.card G) $ l1_2_21' G

lemma l1_2_25' {G : Type*} [group G] : d1_2_24 G ∣ nat.card G :=
begin
  casesI fintype_or_infinite G,
  { rw nat.card_eq_fintype_card,
    exact l1_2_25 },
  { rw nat.card_eq_zero_of_infinite,
    exact dvd_zero _ }
end

noncomputable lemma d1_2_26_ii {G : Type*} [group G] (g h : G) : G := ⁅g, h⁆

lemma n1_2_26_ii {G : Type*} [group G] (g h : G) : ⁅g, h⁆ = ⁅h, g⁆⁻¹ :=
by group

lemma n1_2_26_ii' {G : Type*} [group G] (g h : G) : ⁅g, h⁆ = 1 ↔ g * h = h * g :=
by rw [commutator_element_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, one_mul]

def d1_2_26_iii (G : Type*) [group G] : subgroup G :=
subgroup.closure { (⁅g, h⁆) | (g : G) (h : G) }

lemma l1_2_26_iii' {G : Type*} [group G] :
  (d1_2_26_iii G : set G) = {1} ↔ ∀ (g h : G), g * h = h * g :=
begin
  simp only [d1_2_26_iii],
  rw set.ext_iff,
  simp_rw ←n1_2_26_ii',
  simp only [set_like.mem_coe, set.mem_singleton_iff, set.set_of_exists, subgroup.closure_Union,
    set.set_of_eq_eq_singleton'],
  split,
  { intros h g g',
    rw ←h,
    apply subgroup.mem_supr_of_mem g,
    apply subgroup.mem_supr_of_mem g',
    rw subgroup.mem_closure_singleton,
    use 1,
    rw zpow_one },
  { intros h g,
    split,
    { intro h',
      symmetry,
      simpa only [h, csupr_const, subgroup.mem_closure_singleton, one_zpow, exists_const] using h' },
    { rintro rfl,
      exact subgroup.one_mem _ } }
end

lemma l1_2_26_iii'' {G : Type*} [comm_group G] :
  (d1_2_26_iii G : set G) = {1} :=
l1_2_26_iii'.mpr mul_comm

def l1_2_26_iii''' {G : Type*} [group G] (h : (d1_2_26_iii G : set G) = {1}) : comm_group G :=
{ mul_comm := l1_2_26_iii'.mp h,
  ..show group G, by apply_instance }

lemma ex_1_2_8 {G : Type*} [group G] (h : ∀ g : G, g = 1 ∨ order_of g = 2) (a b : G) :
  a * b = b * a :=
begin
  refine commute_of_order_dvd_two (λ g, _),
  obtain rfl|h := h g,
  { rw order_of_one, exact one_dvd _ },
  { rw ←h },
end

lemma ex_1_2_9
  {G : Type*} [group G] [fintype G]
  (A B : subgroup G) (h : gcd (monoid.exponent A) (monoid.exponent B) = 1) :
  (A : set G) ∩ B = {1} :=
begin
  refine set.eq_singleton_iff_unique_mem.mpr ⟨_, λ x hx, _⟩,
  { apply set.mem_inter;
    { simp only [set_like.mem_coe], exact subgroup.one_mem _ } },
  rw [set.mem_inter_iff, set_like.mem_coe, set_like.mem_coe] at hx,
  rw [←pow_one x, ←h],
  apply pow_gcd_eq_one,
  { rw [←subgroup.coe_mk A x hx.1, ←subgroup.coe_pow, monoid.pow_exponent_eq_one, subgroup.coe_one] },
  { rw [←subgroup.coe_mk B x hx.2, ←subgroup.coe_pow, monoid.pow_exponent_eq_one, subgroup.coe_one] },
end

lemma ex_1_2_10_i (n : ℕ) : nat.card (equiv.perm (fin n)) = n! :=
by rw [nat.card_eq_fintype_card, fintype.card_perm, fintype.card_fin]

example : order_of c[(1 : fin 4), 2] = 2 :=
begin
  apply order_of_eq_prime,
  { simp only [list.form_perm_cons_cons, mul_one, equiv.swap_mul_self, list.form_perm_singleton,
      eq_self_iff_true, sq, cycle.form_perm_coe]},
  { simp [fin.ext_iff] }
end

example : order_of c[(1 : fin 4), 3, 2] ≠ 2 :=
begin
  intro h,
  have := pow_order_of_eq_one c[(1 : fin 4), 3, 2],
  rw [h, sq] at this,
  simp only [cycle.form_perm_coe, list.form_perm_cons_cons, list.form_perm_singleton, mul_one] at this,
  have : (equiv.swap (1 : fin 4) 3 * equiv.swap 3 2 * (equiv.swap 1 3 * equiv.swap 3 2)) 1 = 1,
  { rw this, simp only [id.def, equiv.perm.coe_one, eq_self_iff_true], },
  norm_num at this,
end

lemma ex_1_2_10_ii : nat.card { x : equiv.perm (fin 4) // order_of x = 2 } = 9 :=
begin
  sorry
end

/-
Ex
10 := 22
11 := 23
12 := 25
22. Bepaal de orde van S n . Hoeveel involuties bevat S 4 ? Bepaal exp(S 5 ) en exp(S 6 ).
23. Bepaal de orde van D 2n . Toon aan dat D 2n niet-abels is zodra n ≥ 3.
25. Beschouw de groep S uit Oefening 4 (p. 7). Zoek een oneindige deelgroep G van S,
met de eigenschap dat elk element van G eindige orde heeft, terwijl exp(G) = ∞.
-/