import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Quotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.Int.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

open scoped Nat

/-!
§1. Groups
§1.2 Subgroups and Lagrange's Theorem
-/


def l122Ba {G : Type*} [Group G] (H : Subgroup G) : Group H :=
  inferInstance

theorem l1_2_2_ba' {G : Type*} [Group G] (H : Subgroup G) :
    (∀ a b : H, ((a * b : H) : G) = (a * b : G)) ∧ ((1 : H) : G) = 1 := by
  refine' ⟨_, Subgroup.coe_one _⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  rw [MulMemClass.mk_mul_mk, Subgroup.coe_mk, Subgroup.coe_mk, Subgroup.coe_mk, mul_left_inj]

def l122Ab {G : Type*} [Group G] (H : Set G) [Group H]
    (hmul : ∀ a b : H, ((a * b : H) : G) = (a * b : G)) (h1 : ((1 : H) : G) = 1) :
    Subgroup G where
  carrier := H
  mul_mem' {a b} ha hb := by
    convert Subtype.mem (⟨a, ha⟩ * ⟨b, hb⟩ : H)
    simp [hmul]
  one_mem' := by
    convert Subtype.mem 1
    exact h1.symm
  inv_mem' {x} hx := by
    rw [← Subtype.coe_mk x hx]
    convert Subtype.mem ⟨x, hx⟩⁻¹
    rw [inv_eq_iff_mul_eq_one, ← hmul, mul_right_inv, h1]

theorem l1_2_2_bc {G : Type*} [Group G] (H : Subgroup G) :
    (H : Set G).Nonempty ∧
      ∀ h₁ h₂, h₁ ∈ (H : Set G) → h₂ ∈ (H : Set G) → h₁ * h₂⁻¹ ∈ (H : Set G) := by
  refine' ⟨⟨1, SetLike.mem_coe.mpr (one_mem _)⟩, fun h₁ h₂ h₁mem h₂mem => _⟩
  rw [SetLike.mem_coe] at h₁mem h₂mem ⊢
  exact Subgroup.mul_mem _ h₁mem (Subgroup.inv_mem _ h₂mem)

def l122Cb {G : Type*} [Group G] (H : Set G) (hne : H.Nonempty)
    (hmem : ∀ {h₁ h₂}, h₁ ∈ H → h₂ ∈ H → h₁ * h₂⁻¹ ∈ H) : Subgroup G :=
  have h1 : (1 : G) ∈ H := by
    obtain ⟨x, hx⟩ := hne
    have h1 := hmem hx hx
    rwa [mul_right_inv] at h1
  have hinv : ∀ {h}, h ∈ H → h⁻¹ ∈ H := by
    intro h hh
    convert hmem h1 hh using 1
    rw [one_mul]
  { carrier := H
    mul_mem' := fun {a b} ha hb => by
      convert hmem ha (hinv hb)
      rw [inv_inv]
    one_mem' := h1
    inv_mem' := fun {x} => hinv }

def ex1231 {G : Type*} [Group G] : Subgroup G where
  carrier := {1}
  mul_mem' {a b} ha hb := by
    rw [Set.mem_singleton_iff] at ha hb ⊢
    rw [ha, hb, one_mul]
  one_mem' := Set.mem_singleton _
  inv_mem' {a} ha := by
    rw [Set.mem_singleton_iff] at ha ⊢
    rw [ha, inv_one]

def ex1232 (n : ℤ) : AddSubgroup ℤ :=
  AddSubgroup.zmultiples n

theorem l1_2_3_2 (n : ℤ) : (ex1232 n : Set ℤ) = {k : ℤ | n ∣ k} := by
  ext
  simp [ex1232, Int.mem_zmultiples_iff]

def ex1233 (K : Type*) [Field K] (n : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {A | Matrix.det (A : Matrix (Fin n) (Fin n) K) = (1 : K)}
  mul_mem' {a b} ha hb := by
    rw [Set.mem_setOf] at ha hb ⊢
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ha, hb, one_mul]
  one_mem' := by
    rw [Set.mem_setOf, Matrix.GeneralLinearGroup.coe_one,
      Matrix.det_one]
  inv_mem' {a} ha := by
    rw [Set.mem_setOf] at ha ⊢
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ha, inv_one]

def l124 {G : Type*} [Group G] (S : Set <| Subgroup G) : Subgroup G :=
  sInf S

theorem l1_2_4' {G : Type*} [Group G] (S : Set <| Subgroup G) :
    (l124 S : Set G) = ⋂ s ∈ S, (s : Set G) :=
  Subgroup.coe_sInf _

def d125 {G : Type*} [Group G] (X : Set G) : Subgroup G :=
  Subgroup.closure X

theorem l1_2_5' {G : Type*} [Group G] (X : Set G) :
    (Subgroup.closure X : Set G) = ⋂ H' ∈ {H : Subgroup G | X ⊆ H}, (H' : Set G) :=
  rfl

def n125Set {G : Type*} [Group G] (X : Set G) : Set (List G) :=
  {m : List G | ∀ x ∈ m, x ∈ X ∪ X⁻¹}

def n125 {G : Type*} [Group G] (X : Set G) : Subgroup G where
  carrier := { (List.prod x) | x ∈ n125Set X }
  mul_mem' {a b} ha hb := by
    simp [Set.mem_setOf] at ha hb ⊢
    obtain ⟨xa, hxa⟩ := ha
    obtain ⟨xb, hxb⟩ := hb
    refine' ⟨xa ++ xb, _, _⟩
    · simp only [n125Set, Set.mem_setOf] at hxa hxb ⊢
      intro x hx
      obtain hx' | hx' := List.mem_append.mp hx
      exacts [hxa.1 x hx', hxb.1 x hx']
    · rw [List.prod_append, hxa.2, hxb.2]
  one_mem' := by
    simp [Set.mem_setOf]
    refine' ⟨[], _, List.prod_nil⟩
    simp [n125Set, Set.mem_setOf]
  inv_mem' := by
    intro a ha
    simp [Set.mem_setOf] at ha ⊢
    obtain ⟨xa, hxa⟩ := ha
    refine' ⟨(xa.map Inv.inv).reverse, _, _⟩
    · rw [n125Set, Set.mem_setOf] at hxa ⊢
      intro x hx
      rw [List.mem_reverse, List.mem_map, inv_involutive.exists_mem_and_apply_eq_iff] at hx
      simpa [or_comm] using hxa.1 _ hx
    · rw [← hxa.2, List.prod_inv_reverse]

-- 2019-2020
theorem n1_2_5' {G : Type*} [Group G] (X : Set G) :
    (Subgroup.closure X : Set G) = { (List.prod x) | x ∈ n125Set X } := by
  simp only [Subgroup.closure, Subgroup.coe_sInf]
  apply subset_antisymm
  · intro x hx
    simp only [Set.mem_iInter] at hx
    simp only [Set.mem_setOf]
    specialize hx (n125 X) _
    · intro y hy
      simp only [n125, Set.mem_setOf, Subgroup.coe_set_mk]
      refine' ⟨[y], _, List.prod_singleton⟩
      simp only [hy, n125Set, forall_eq, true_or_iff, Set.mem_setOf, List.mem_singleton,
        Set.mem_union]
    simpa [n125] using hx
  · intro x hx
    simp only [Set.mem_setOf, n125Set] at hx
    simp only [Set.mem_iInter, SetLike.mem_coe]
    intro i hi
    obtain ⟨y, h1, rfl⟩ := hx
    induction y with
    | nil =>
      simp only [List.prod_nil, one_mem]
    | cons y_hd tail y_ih =>
      simp only [List.prod_cons]
      apply mul_mem
      · specialize h1 y_hd (List.mem_cons_self _ _)
        obtain h1 | h1 := (Set.mem_union _ _ _).mp h1
        · exact hi h1
        · rw [← inv_inv y_hd]; exact Subgroup.inv_mem _ (hi h1)
      · exact y_ih fun y hy => h1 _ (List.mem_cons_of_mem _ hy)

def l128A {G : Type*} [Group G] (H : Subgroup G) : Setoid G :=
  QuotientGroup.leftRel H

theorem l1_2_8_b {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G :=
  Subgroup.card_subgroup_dvd_card H

open scoped Cardinal

theorem l1_2_9 {G : Type*} [Group G] (H : Subgroup G) :
    #(Quotient (QuotientGroup.rightRel H)) = #(Quotient (QuotientGroup.leftRel H)) :=
  Cardinal.mk_congr <| QuotientGroup.quotientRightRelEquivQuotientLeftRel H

def d1210 {G : Type*} [Group G] (H : Subgroup G) :=
  #(G ⧸ H)

theorem d1_2_10' {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card (G ⧸ H) = Nat.card G / Nat.card H := by
  have : Fintype H := by classical infer_instance
  have : 0 < Nat.card H := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
    exact ⟨⟨1, one_mem _⟩⟩
  rw [← Subgroup.card_mul_index H, Nat.mul_div_cancel_left _ this, Subgroup.index]

theorem xmp_1_2_11 (n : ℕ+) : AddSubgroup.index (ex1232 n) = n := by
  simp [ex1232, AddSubgroup.index, Nat.card_congr (Int.quotientZmultiplesNatEquivZMod n).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

theorem n_1_2_13 {G : Type*} [Group G] (A B : Set G) (g : G) :
    A = { (g * b) | b ∈ B } ↔ { (g⁻¹ * a) | a ∈ A } = B := by constructor <;> · rintro rfl; ext; simp

def ex124' {G : Type*} [Group G] (x : G × G) :=
  x.1 * x.2

theorem ex_1_2_4 {G : Type*} [Group G] (A B : Set G) :
  #({ (ex124' x) | x ∈ A ×ˢ B} : Set G) ≤ #A * #B := by
  simp only [ex124', Set.mem_prod, exists_prop, Prod.exists]
  calc
    (#{x | ∃ a b : G, (a ∈ A ∧ b ∈ B) ∧ a * b = x}) =
        (#(⋃ (a ∈ A) (b ∈ B), ({(a : G) * (b : G)} : Set G))) := ?_
    _ = (#(⋃ (a : A) (b : B), ({(a : G) * (b : G)} : Set G))) := ?_
    _ ≤ Cardinal.sum fun a : A => Cardinal.sum fun b : B => #({(a : G) * (b : G)} : Set G) := ?_
    _ = (#A) * (#B) := ?_
  · congr 2 with x
    simp [Set.setOf_exists, Set.setOf_and, and_assoc]
  · simp only [Set.iUnion_coe_set]
  · exact
      Cardinal.mk_iUnion_le_sum_mk.trans
        (Cardinal.sum_le_sum _ _ fun a => Cardinal.mk_iUnion_le_sum_mk)
  · simp_rw [Cardinal.mk_singleton, Cardinal.sum_const', mul_one]

theorem ex_1_2_5 {G : Type*} [Group G] (A B : Set G) (g : G) :
    { (g * x) | x ∈ A ∩ B } = { (g * x) | x ∈ A } ∩ { (g * x) | x ∈ B } := by
  ext y; simp only [Set.mem_inter, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨x, ⟨ha, hb⟩, hx⟩
    exact ⟨⟨x, ha, hx⟩, ⟨x, hb, hx⟩⟩
  · rintro ⟨⟨x, ha, hx⟩, ⟨x', hb, hx'⟩⟩
    obtain rfl : x = x' := by rw [← mul_right_inj g, hx, hx']
    exact ⟨x, ⟨ha, hb⟩, hx⟩

theorem ex_1_2_6 {G : Type*} [Fintype G] [Group G] (A B : Subgroup G) (h : A ≤ B) :
    Subgroup.index A = Subgroup.relindex A B * Subgroup.index B :=
  (Subgroup.relindex_mul_index h).symm

theorem ex_1_2_7 {G : Type*} [Group G] (A B : Subgroup G) (h : A ≤ B) :
    Subgroup.index A = Subgroup.relindex A B * Subgroup.index B :=
  (Subgroup.relindex_mul_index h).symm

def d1214 (G : Type*) [Group G] (g : G) (n : ℤ) :=
  g ^ n

theorem l1_2_15_i (G : Type*) [Group G] (g : G) (m n : ℤ) : g ^ (m + n) = g ^ m * g ^ n :=
  zpow_add g m n

theorem l1_2_15_i' (G : Type*) [Group G] (g : G) (m n : ℤ) : (g ^ m) ^ n = g ^ (m * n) :=
  (zpow_mul g m n).symm

theorem l1_2_15_ii (G : Type*) [Group G] (g : G) :
    (Subgroup.closure ({g} : Set G) : Set G) = { (g ^ k) | k : ℤ } := by
  ext
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Subgroup.mem_closure_singleton]

theorem l1_2_17 (G : Type*) [Group G] (g a b : G)
    (ha : a ∈ Subgroup.closure ({g} : Set G)) (hb : b ∈ Subgroup.closure ({g} : Set G)) :
    a * b = b * a := by
  rw [Subgroup.mem_closure_singleton] at ha hb
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  rw [← zpow_add, ← zpow_add, add_comm]

theorem l1_2_19 (G : Type*) [Group G] (g : G) (d : ℤ) : g ^ d = 1 ↔ (orderOf g : ℤ) ∣ d :=
  orderOf_dvd_iff_zpow_eq_one.symm

theorem l1_2_20_i (G : Type*) [Group G] (g : G) (i j : ℤ) (_h : IsOfFinOrder g) :
    g ^ i = g ^ j ↔ i ≡ j [ZMOD orderOf g] :=
  zpow_eq_zpow_iff_modEq

namespace Subgroup

theorem mem_closure_singleton' {G : Type*} [Group G] {x y : G} (h : IsOfFinOrder x) :
    y ∈ closure ({x} : Set G) ↔ ∃ n < orderOf x, x ^ n = y := by
  simp only [← zpowers_eq_closure, exists_prop]
  constructor <;>
  rintro ⟨i, hi⟩
  · suffices ∃ n : ℤ, 0 ≤ n ∧ n < orderOf x ∧ x ^ n = y by
      obtain ⟨n, hnonneg, hlt, heq⟩ := this
      refine' ⟨n.natAbs, _, _⟩
      · rwa [← Int.ofNat_lt, Int.natAbs_of_nonneg hnonneg]
      · rwa [← zpow_ofNat, Int.natAbs_of_nonneg hnonneg]
    have ho : 0 < (orderOf x : ℤ) := by
      rwa [Int.coe_nat_pos, pos_iff_ne_zero, Ne.def, orderOf_eq_zero_iff, Classical.not_not]
    refine' ⟨i % orderOf x, Int.emod_nonneg _ ho.ne', Int.emod_lt_of_pos _ ho, _⟩
    rw [← hi, l1_2_20_i _ _ _ _ h]
    exact Int.mod_modEq _ _
  · use i
    simp only [zpow_ofNat, hi.2]

end Subgroup

theorem l1_2_20_i' (G : Type*) [Group G] (g : G) (h : IsOfFinOrder g) :
    (Subgroup.closure ({g} : Set G) : Set G) = { (g ^ i) | i ∈ Set.Ico 0 (orderOf g) } := by ext; simp [Subgroup.mem_closure_singleton' h]

theorem l1_2_20_ii (G : Type*) [Group G] (g : G) (i j : ℤ) (h : ¬IsOfFinOrder g) :
    g ^ i = g ^ j ↔ i = j := by
  rw [← orderOf_eq_zero_iff] at h
  rw [zpow_eq_zpow_iff_modEq, h, Int.ofNat_zero, Int.modEq_zero_iff]

theorem l1_2_20_ii' (G : Type*) [Group G] (g : G) (_h : ¬IsOfFinOrder g) :
    (Subgroup.closure ({g} : Set G) : Set G) = { (g ^ i) | i : ℤ } := by
  rw [← Subgroup.zpowers_eq_closure]
  ext; simp [Subgroup.mem_zpowers_iff]

theorem l1_2_20_iii (G : Type*) [Group G] (g : G) (h : IsOfFinOrder g) :
    (#(Subgroup.closure ({g} : Set G) : Set G)) = orderOf g := by
  classical
  have := (IsOfFinOrder.orderOf_pos h).ne'
  rw [l1_2_20_i' _ _ h]
  trans #((Set.Ico 0 (orderOf g)).image fun i => g ^ i)
  · congr
  simp only [Cardinal.mk_fintype, Nat.cast_inj, Fintype.card_ofFinset]
  rw [Finset.card_image_of_injOn]
  simp only [tsub_zero, eq_self_iff_true, Set.toFinset_card, Nat.card_fintypeIco]
  intro x hx y hy hxy
  rwa [pow_eq_pow_iff_modEq, Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at hxy
  simpa using hy
  simpa using hx

section

universe u v

variable {G : Type u} {A : Type v}

variable {x y : G} {a b : A} {n m : ℕ}

variable [Group G] [AddGroup A] {i : ℤ}

theorem zpow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : ℤ} : x ^ n = x ^ m ↔ n = m := by
  rw [orderOf_eq_zero_iff] at h
  exact l1_2_20_ii _ _ n m h

end

theorem l1_2_20_iii' (G : Type*) [Group G] (g : G) (h : ¬IsOfFinOrder g) :
    Set.Infinite (Subgroup.closure ({g} : Set G) : Set G) := by
  rw [l1_2_20_ii' _ _ h]
  rw [← orderOf_eq_zero_iff] at h
  have : ((Set.univ : Set ℕ).image fun i => g ^ i).Infinite := by
    simp
    apply Set.infinite_range_of_injective
    intro x y hxy
    rwa [pow_inj_iff_of_orderOf_eq_zero h] at hxy
  apply Set.Infinite.mono _ this
  intro x hx
  simp only [Set.image_univ, Set.mem_range] at hx
  simp only [Set.mem_setOf]
  obtain ⟨n, hn⟩ := hx
  use n
  simp only [zpow_ofNat, hn]

theorem l1_2_21 (G : Type*) [Group G] [Fintype G] (g : G) : orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card

theorem l1_2_21' (G : Type*) [Group G] [Fintype G] (g : G) : g ^ Fintype.card G = 1 :=
  pow_card_eq_one

namespace Int

theorem gcd_val (a b : ℤ) : gcd a b = gcd (b % a) a := by
  rw [← natAbs_euclideanDomain_gcd, EuclideanDomain.gcd_val, natAbs_euclideanDomain_gcd]

end Int

theorem coe_mul_inv_eq_one'' {n : ℕ} (x : Int) (h : IsCoprime x n) : (x * (↑x)⁻¹ : ZMod n) = 1 := by
  cases n with
  | zero =>
    simp [isCoprime_zero_right] at h
    rw [ZMod.mul_inv_eq_gcd, Nat.gcd_zero_right, Nat.cast_eq_one]
    simp only [ZMod.val]
    rw [Int.cast_id, Int.IsUnit.natAbs_eq h]
  | succ n =>
    haveI := n.succ_pos
    rw [← Int.gcd_eq_one_iff_coprime, Int.gcd_comm, Int.gcd_val] at h
    rw [ZMod.mul_inv_eq_gcd, ← Int.coe_nat_gcd, ZMod.val_int_cast, h, Nat.cast_one]

def unitOfIsCoprime' {n : ℕ} (x : ℤ) (h : IsCoprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one'' x h, by rw [mul_comm, coe_mul_inv_eq_one'' x h]⟩

@[simp]
theorem coe_unitOfIsCoprime' {n : ℕ} (x : ℤ) (h : IsCoprime x n) :
    (unitOfIsCoprime' x h : ZMod n) = x :=
  rfl

@[simp]
theorem ZMod.pow_totient' {n : ℕ} (x : (ZMod n)ˣ) : x ^ Nat.totient n = 1 := by
  cases n
  · simp
  apply ZMod.pow_totient

theorem l1_2_23 (n : ℕ+) (x : ℤ) (h : IsCoprime x n) : x ^ Nat.totient n ≡ 1 [ZMOD n] := by
  rw [← CharP.intCast_eq_intCast (ZMod n), Int.cast_pow, Int.cast_one, ←
    coe_unitOfIsCoprime' _ h, ← Units.val_pow_eq_pow_val, Units.val_eq_one, ← ZMod.pow_totient' _]

noncomputable def d1224 (G : Type*) [Group G] : ℕ :=
  Monoid.exponent G

theorem d1224_dvd {G : Type*} [Group G] (g : G) : orderOf g ∣ d1224 G :=
  Monoid.order_dvd_exponent g

theorem d1224_dvd' {G : Type*} [Group G] (n : ℕ) (h : ∀ g : G, orderOf g ∣ n) : d1224 G ∣ n :=
  Monoid.exponent_dvd_of_forall_pow_eq_one G n <|
    forall_imp (fun _ => orderOf_dvd_iff_pow_eq_one.mp) h

@[to_additive]
theorem commute_of_order_dvd_two {G : Type*} [Monoid G] [IsCancelMul G] {a b : G} (h : ∀ g : G, orderOf g ∣ 2) :
    a * b = b * a := by
  simp_rw [orderOf_dvd_iff_pow_eq_one] at h
  rw [← mul_right_inj a, ← mul_left_inj b]
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by simp only [pow_two]; group
    _ = 1 := by rw [h, h, mul_one]
    _ = (a * b) ^ 2 := by rw [h]
    _ = a * (b * a) * b := by simp only [pow_two]; group
theorem commute_of_order_dvd_two' {G : Type*} [Group G] {a b : G} (h : ∀ g : G, orderOf g ∣ 2) :
    a * b = b * a := commute_of_order_dvd_two h

example {G : Type*} [Group G] (h : Monoid.exponent G = 2) (a b : G) : a * b = b * a :=
  mul_comm_of_exponent_two h a b
@[to_additive]
lemma mul_comm_of_exponent_two'  {G : Type*} [Group G]  (hG : Monoid.exponent G = 2) (x y : G) :
    x * y = y * x :=
  commute_of_order_dvd_two fun g => hG ▸ Monoid.order_dvd_exponent g

theorem n1_2_24 :
    ∃ (G : Type) (_ : AddGroup G), (∀ g : G, IsOfFinAddOrder g) ∧ AddMonoid.exponent G = 0 := by
  refine' ⟨ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ), inferInstance, fun g => _, _⟩
  · induction g using QuotientAddGroup.induction_on' with | H g => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine' ⟨g.den, g.pos, _⟩
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_zmultiples_iff]
    use g.num
    rw [Int.smul_one_eq_coe, ← Rat.mul_den_eq_num, mul_comm]
  · rw [AddMonoid.exponent_eq_zero_iff, AddMonoid.ExponentExists]
    push_neg
    refine' fun n hn => ⟨(1 / (2 * n) : ℚ), _⟩
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, Ne.def, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_zmultiples_iff, not_exists]
    refine' fun x => ne_of_apply_ne Rat.den _
    rw [Int.smul_one_eq_coe, Rat.coe_int_den, one_div, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel ((@Nat.cast_ne_zero ℚ _ _ _).mpr hn.ne'), one_mul, ← Int.cast_two,
      Rat.inv_coe_int_den]
    norm_num; decide

theorem n1_2_24' {G : Type*} [Group G] [Fintype G] : d1224 G ≠ 0 :=
  Monoid.exponent_ne_zero_of_finite

theorem l1_2_25 {G : Type*} [Group G] [Fintype G] : d1224 G ∣ Fintype.card G :=
  Monoid.exponent_dvd_of_forall_pow_eq_one G (Fintype.card G) <| l1_2_21' G

theorem l1_2_25' {G : Type*} [Group G] : d1224 G ∣ Nat.card G := by
  cases fintypeOrInfinite G
  · rw [Nat.card_eq_fintype_card]
    exact l1_2_25
  · rw [Nat.card_eq_zero_of_infinite]
    exact dvd_zero _

noncomputable def d1226Ii {G : Type*} [Group G] (g h : G) : G :=
  ⁅g, h⁆

theorem n1_2_26_ii {G : Type*} [Group G] (g h : G) : ⁅g, h⁆ = ⁅h, g⁆⁻¹ := by group

theorem n1_2_26_ii' {G : Type*} [Group G] (g h : G) : ⁅g, h⁆ = 1 ↔ g * h = h * g := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, one_mul]

def d1226Iii (G : Type*) [Group G] : Subgroup G :=
  Subgroup.closure { (⁅g, h⁆) | (g : G) (h : G) }

theorem l1_2_26_iii' {G : Type*} [Group G] :
    (d1226Iii G : Set G) = {1} ↔ ∀ g h : G, g * h = h * g := by
  simp only [d1226Iii]
  rw [Set.ext_iff]
  simp_rw [← n1_2_26_ii']
  simp only [SetLike.mem_coe, Set.mem_singleton_iff, Set.setOf_exists, Subgroup.closure_iUnion,
    Set.setOf_eq_eq_singleton']
  constructor
  · intro h g g'
    rw [← h]
    apply Subgroup.mem_iSup_of_mem g
    apply Subgroup.mem_iSup_of_mem g'
    rw [Subgroup.mem_closure_singleton]
    use 1
    rw [zpow_one]
  · intro h g
    constructor
    · intro h'
      symm
      simpa only [h, ciSup_const, Subgroup.mem_closure_singleton, one_zpow, exists_const] using h'
    · rintro rfl
      exact Subgroup.one_mem _

theorem l1_2_26_iii'' {G : Type*} [CommGroup G] : (d1226Iii G : Set G) = {1} :=
  l1_2_26_iii'.mpr mul_comm

def l1226Iii''' {G : Type*} [Group G] (h : (d1226Iii G : Set G) = {1}) : CommGroup G :=
  { show Group G by infer_instance with mul_comm := l1_2_26_iii'.mp h }

theorem ex_1_2_8 {G : Type*} [Group G] (h : ∀ g : G, g = 1 ∨ orderOf g = 2) (a b : G) :
    a * b = b * a := by
  refine' commute_of_order_dvd_two fun g => _
  obtain rfl | h := h g
  · rw [orderOf_one]; exact one_dvd _
  · rw [← h]

theorem ex_1_2_9 {G : Type*} [Group G] [Fintype G] (A B : Subgroup G)
    (h : gcd (Monoid.exponent A) (Monoid.exponent B) = 1) : (A : Set G) ∩ B = {1} := by
  refine' Set.eq_singleton_iff_unique_mem.mpr ⟨_, fun x hx => _⟩
  · apply Set.mem_inter <;> · simp only [SetLike.mem_coe]; exact Subgroup.one_mem _
  rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe] at hx
  rw [← pow_one x, ← h]
  apply pow_gcd_eq_one
  · rw [← Subgroup.coe_mk A x hx.1, ← Subgroup.coe_pow, Monoid.pow_exponent_eq_one,
      Subgroup.coe_one]
  · rw [← Subgroup.coe_mk B x hx.2, ← Subgroup.coe_pow, Monoid.pow_exponent_eq_one,
      Subgroup.coe_one]

theorem ex_1_2_10_i (n : ℕ) : Nat.card (Equiv.Perm (Fin n)) = n ! := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem ex_1_2_10_ii_aux_1 (x : Equiv.Perm (Fin 4)) :
    orderOf x = 2 ↔ x ≠ 1 ∧ x ^ 2 = 1 := by
  rw [orderOf_eq_iff two_pos]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    have := h2 1 one_lt_two one_pos
    rwa [pow_one] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    intros m hm1 hm2
    obtain rfl : m = 1 := by linarith
    rwa [pow_one]

example : orderOf c[(1 : Fin 4), 2] = 2 := by
  rw [ex_1_2_10_ii_aux_1]; decide

example : orderOf c[(1 : Fin 4), 3, 2] ≠ 2 := by
  rw [Ne, ex_1_2_10_ii_aux_1]; decide

theorem ex_1_2_10_ii : Nat.card { x : Equiv.Perm (Fin 4) // orderOf x = 2 } = 9 := by
  rw [Nat.card_eq_fintype_card]
  simp_rw [ex_1_2_10_ii_aux_1]
  decide

theorem Monoid.exponent_dvd_card {G : Type*} [Group G] [Fintype G] :
    Monoid.exponent G ∣ Fintype.card G :=
  l1_2_25

theorem Monoid.ExponentExists.ofFinite (G : Type*) [Group G] [Finite G] : Monoid.ExponentExists G := by
  let _inst := Fintype.ofFinite
  simp only [Monoid.ExponentExists]
  refine ⟨Fintype.card G, Fintype.card_pos, fun g => ?_⟩
  · rw [← orderOf_dvd_iff_pow_eq_one]
    exact orderOf_dvd_card

theorem Monoid.ExponentExists.ofFintype (α : Type*) [Group α] [Fintype α] : Monoid.ExponentExists α := by
  simp only [Monoid.ExponentExists]
  refine ⟨Fintype.card α, Fintype.card_pos, fun g => ?_⟩
  · rw [← orderOf_dvd_iff_pow_eq_one]
    exact orderOf_dvd_card

-- Bepaal exp(S_5) en exp(S_6).
-- TODO: bewijs
#eval Nat.find (Monoid.ExponentExists.ofFintype (Equiv.Perm (Fin 5)))
#eval Nat.find (Monoid.ExponentExists.ofFintype (Equiv.Perm (Fin 6)))

theorem ex_1_2_11_i (n : ℕ) : Nat.card (DihedralGroup n) = 2 * n :=
  DihedralGroup.nat_card

theorem Nat.card_subtype {α : Type u_1} [inst : Fintype α] (p : α → Prop) [ DecidablePred p] :
    Nat.card { x // p x } = Finset.card (Finset.filter p Finset.univ) := by
  rw [← Fintype.card_subtype]
  rw [@card_eq_fintype_card]

theorem ZMod.val_ofNat {n : ℕ} (a : ℕ) [a.AtLeastTwo] :
    (no_index (OfNat.ofNat a) : ZMod n).val = a % n :=
  val_nat_cast a

theorem ZMod.val_ofNat_of_lt {n a : ℕ} [a.AtLeastTwo] (h : a < n) :
    (no_index (OfNat.ofNat a) : ZMod n).val = a :=
  val_nat_cast_of_lt h

open DihedralGroup in
theorem ex_1_2_11_ii {n : ℕ} (hn : 3 ≤ n) : ¬ IsCommutative (DihedralGroup n) (· * ·) := by
  rintro ⟨h⟩
  have := h (r 1) (sr 0)
  simp only [r_mul_sr, zero_sub, sr_mul_r, zero_add, sr.injEq] at this
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, ← ZMod.val_eq_zero, ZMod.val_ofNat_of_lt hn] at this
  contradiction

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
