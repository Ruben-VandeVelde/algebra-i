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
{ carrier := { k : ℤ | n ∣ k },
  add_mem' := λ a b ha hb, by {
    rw [set.mem_set_of] at ha hb ⊢,
    exact dvd_add ha hb },
  zero_mem' := set.mem_set_of.mpr $ dvd_zero _,
  neg_mem' := λ a ha, by {
    rw [set.mem_set_of] at ha ⊢,
    exact (dvd_neg _ _).mpr ha } }

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

def l1_2_4 {G : Type*} [group G] (S : set $ subgroup G) : subgroup G :=
{ carrier := ⋂ (H : subgroup  G) (HH : H ∈ S), (H : set G),
  mul_mem' := λ a b ha hb, by {
    simp only [set.mem_Inter, set_like.mem_coe] at ha hb ⊢,
    exact λ H HH, subgroup.mul_mem H (ha H HH) (hb H HH) },
  one_mem' := by {
    simp only [set.mem_Inter, set_like.mem_coe],
    exact λ H HH, one_mem _ },
  inv_mem' := λ a ha, by {
    simp only [set.mem_Inter, set_like.mem_coe] at ha ⊢,
    exact λ H HH, subgroup.inv_mem _ (ha H HH), } }
