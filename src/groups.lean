import analysis.inner_product_space.pi_L2
import data.zmod.basic
import group_theory.specific_groups.dihedral
import linear_algebra.general_linear_group

section

variables {M A G : Type*}

variables [group G] {a b c: G}

lemma l1_1_3_i (f:G) (h1: ∀ g, f * g = g) (h2: ∀ g, g * f = g) : f = 1 :=
begin
  rw [←@self_eq_mul_left _ _ _ f, h1],
end

lemma l1_1_3_ii (g a b:G) (h1: a * g = 1) (h2: 1 = g * b) : a = b :=
left_inv_eq_right_inv h1 h2.symm

lemma l1_1_4 (g:G) : (g ⁻¹)⁻¹ = g :=
inv_inv _

lemma l1_1_5_i (x y z: G) : x * y = x * z → y = z :=
begin
  intro h,
  rwa ←mul_left_cancel_iff,
end

lemma l1_1_5_ii (x y z: G) : x * z = y * z → x = y :=
begin
  intro h,
  rwa ←mul_right_cancel_iff,
end

def l1_1_6_1 : add_comm_group ℤ := infer_instance

def mulint (n:int) := {k : ℤ // n ∣ k}

namespace mulint

def add (k:int) : mulint k → mulint k → mulint k
| ⟨z, hz⟩ ⟨ z', hz'⟩ := ⟨int.add z z', dvd_add hz hz'⟩

end mulint

-- TODO: add_zero_class short-circuit in data/int/basic.lean?

noncomputable def l1_1_6_2 (n : ℤ) : add_comm_group $ mulint n :=
{ add := mulint.add n,
  add_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, subtype.eq $ add_assoc a b c,
  zero := ⟨0, dvd_zero _⟩,
  zero_add := λ ⟨a, ha⟩, subtype.eq $ zero_add a,
  add_zero := λ ⟨a, ha⟩, subtype.eq $ add_zero a,
  neg := λ ⟨a, ha⟩, ⟨-a, (dvd_neg n a).mpr ha⟩,
  add_left_neg := λ ⟨a, ha⟩, subtype.eq $ add_left_neg a,
  add_comm := λ ⟨a, ha⟩ ⟨b, hb⟩, subtype.eq $ add_comm a b, }

def l1_1_6_3 (m : ℕ) : add_comm_group $ zmod m := infer_instance
def l1_1_6_4 (m : ℕ) : comm_group $ (zmod m)ˣ := infer_instance
def l1_1_6_5 : comm_group $ ℤˣ := infer_instance

inductive trivial_group
| One

instance : unique trivial_group :=
{ default := trivial_group.One,
  uniq := λ a, trivial_group.rec_on a rfl }

def l1_1_6_6 : comm_group trivial_group :=
{ one := trivial_group.One,
  mul := λ a b, trivial_group.One,
  inv := λ a, trivial_group.One,
  mul_assoc := λ a b c, subsingleton.elim _ _,
  one_mul := λ a, subsingleton.elim _ _,
  mul_one := λ a, subsingleton.elim _ _,
  mul_left_inv := λ a, subsingleton.elim _ _,
  mul_comm := λ a b, subsingleton.elim _ _ }

def l1_1_6_7 (K V : Type*) [field K] [add_comm_monoid V] [module K V] :
  add_comm_group V := module.add_comm_monoid_to_add_comm_group K

def l1_1_6_8 (K V : Type*) [field K] (n : ℕ) :
  group $ matrix.general_linear_group (fin n) K := units.group

noncomputable def l1_1_6_8' (K V n : Type*) [field K] [subsingleton n] :
  comm_group $ matrix.general_linear_group n K :=
{ mul_comm := λ a b, by
  { ext i j,
    haveI : unique n := unique_of_subsingleton i,
    simp only [matrix.general_linear_group.coe_mul, matrix.mul_apply, finset.univ_unique,
      finset.sum_singleton],
    rw [subsingleton.elim default i, subsingleton.elim j i, mul_comm] },
  ..(infer_instance : group _) }

noncomputable def l1_1_6_8'' (K V n : Type*) [comm_semiring K] [subsingleton n] :
  comm_monoid $ matrix n n K :=
{ mul_comm := λ a b, by
  { rw [matrix.mul_eq_mul, matrix.mul_eq_mul],
    ext i j,
    haveI : unique n := unique_of_subsingleton i,
    simp [matrix.general_linear_group.coe_mul, matrix.mul_apply, finset.univ_unique,
      finset.sum_singleton],
    rw [subsingleton.elim default i, subsingleton.elim j i, mul_comm] },
  ..(infer_instance : monoid _) }

def l1_1_6_9 (α : Type*) (X : set α) : group (equiv.perm X) := infer_instance

noncomputable def l1_1_6_10 (n : ℕ) :
  group $ isometric (euclidean_space ℝ (fin n)) (euclidean_space ℝ (fin n)) := infer_instance

def l1_1_6_11 (n : ℕ) : group (dihedral_group n) := infer_instance

end

lemma ex_1_1_1 {G : Type*} [group G] (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
