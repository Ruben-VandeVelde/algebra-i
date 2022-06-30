import data.zmod.quotient
import group_theory.subgroup.basic
import linear_algebra.general_linear_group

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
