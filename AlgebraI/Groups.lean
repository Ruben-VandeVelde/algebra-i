import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

#align_import groups

/-!
§1. Groups
§1.1 Definition and examples
-/


section

variable {M A G : Type _}

variable [Group G] {a b c : G}

theorem l1_1_3_i (f : G) (h1 : ∀ g, f * g = g) (h2 : ∀ g, g * f = g) : f = 1 := by
  rw [← @self_eq_mul_left _ _ _ f, h1]

theorem l1_1_3_ii (g a b : G) (h1 : a * g = 1) (h2 : 1 = g * b) : a = b :=
  left_inv_eq_right_inv h1 h2.symm

theorem l1_1_4 (g : G) : g⁻¹⁻¹ = g :=
  inv_inv _

theorem l1_1_5_i (x y z : G) : x * y = x * z → y = z :=
  by
  intro h
  rwa [← mul_left_cancel_iff]

theorem l1_1_5_ii (x y z : G) : x * z = y * z → x = y :=
  by
  intro h
  rwa [← mul_right_cancel_iff]

def l1161 : AddCommGroup ℤ :=
  inferInstance

def Mulint (n : Int) :=
  { k : ℤ // n ∣ k }

namespace Mulint

def add (k : Int) : Mulint k → Mulint k → Mulint k
  | ⟨z, hz⟩, ⟨z', hz'⟩ => ⟨Int.add z z', dvd_add hz hz'⟩

end Mulint

-- TODO: add_zero_class short-circuit in data/int/basic.lean?
def l1162 (n : ℤ) : AddCommGroup <| Mulint n
    where
  add := Mulint.add n
  add_assoc := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ => Subtype.eq <| add_assoc a b c
  zero := ⟨0, dvd_zero _⟩
  zero_add := fun ⟨a, ha⟩ => Subtype.eq <| zero_add a
  add_zero := fun ⟨a, ha⟩ => Subtype.eq <| add_zero a
  neg := fun ⟨a, ha⟩ => ⟨-a, dvd_neg.mpr ha⟩
  add_left_neg := fun ⟨a, ha⟩ => Subtype.eq <| add_left_neg a
  add_comm := fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.eq <| add_comm a b

def l1163 (m : ℕ) : AddCommGroup <| ZMod m :=
  inferInstance

def l1164 (m : ℕ) : CommGroup <| (ZMod m)ˣ :=
  inferInstance

def l1165 : CommGroup <| ℤˣ :=
  inferInstance

inductive TrivialGroup
  | One

instance : Unique TrivialGroup where
  default := TrivialGroup.One
  uniq a := TrivialGroup.recOn a rfl

def l1166 : CommGroup TrivialGroup where
  one := TrivialGroup.One
  mul a b := TrivialGroup.One
  inv a := TrivialGroup.One
  mul_assoc a b c := Subsingleton.elim _ _
  one_mul a := Subsingleton.elim _ _
  mul_one a := Subsingleton.elim _ _
  hMul_left_inv a := Subsingleton.elim _ _
  mul_comm a b := Subsingleton.elim _ _

def l1167 (K V : Type _) [Field K] [AddCommMonoid V] [Module K V] : AddCommGroup V :=
  Module.addCommMonoidToAddCommGroup K

def l1168 (K : Type _) [Field K] (n : ℕ) : Group <| Matrix.GeneralLinearGroup (Fin n) K :=
  Units.group

def l1168' (K n : Type _) [Field K] [Subsingleton n] [Fintype n] :
    CommGroup <| Matrix.GeneralLinearGroup n K :=
  { (inferInstance : Group _) with
    mul_comm := fun a b => by
      ext i j
      haveI : Unique n := uniqueOfSubsingleton i
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Finset.univ_unique,
        Finset.sum_singleton]
      rw [Subsingleton.elim default i, Subsingleton.elim j i, mul_comm] }

def l1168'' (K n : Type _) [CommSemiring K] [Subsingleton n] [Fintype n] :
    CommMonoid <| Matrix n n K :=
  { (inferInstance : Monoid _) with
    mul_comm := fun a b => by
      rw [Matrix.hMul_eq_hMul, Matrix.hMul_eq_hMul]
      ext i j
      haveI : Unique n := uniqueOfSubsingleton i
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Finset.univ_unique,
        Finset.sum_singleton]
      rw [Subsingleton.elim default i, Subsingleton.elim j i, mul_comm] }

def l1169 (α : Type _) (X : Set α) : Group (Equiv.Perm X) :=
  inferInstance

noncomputable def l11610 (n : ℕ) :
    Group <| IsometryEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

def l11611 (n : ℕ) : Group (DihedralGroup n) :=
  inferInstance

end

theorem ex_1_1_1 {G : Type _} [Group G] (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  mul_inv_rev _ _

namespace Ex112

variable {G : Type _} [One G] [Mul G] [Inv G] [IsAssociative G (· * ·)] (h1 : ∀ a : G, a * 1 = a)
  (h2 : ∀ a : G, a * a⁻¹ = 1)

-- Based on https://math.stackexchange.com/questions/537572/any-set-with-associativity-left-identity-left-inverse-is-a-group
theorem one_hMul (a : G) : 1 * a = a :=
  by
  have : a * (a⁻¹ * a) * a⁻¹ = a * (a * a⁻¹) * a⁻¹ :=
    by
    calc
      a * (a⁻¹ * a) * a⁻¹ = a * a⁻¹ * (a * a⁻¹) := _
      _ = a * a⁻¹ * 1 := _
      _ = a * 1 * a⁻¹ := _
      _ = a * (a * a⁻¹) * a⁻¹ := _
    · rw [← @IsAssociative.assoc _ (· * ·), ← @IsAssociative.assoc _ (· * ·)]
    · rw [h2]
    · rw [h1, h1]
    · rw [h2]
  have : a * (a⁻¹ * a) = a * (a * a⁻¹) :=
    by
    have := congr_arg (· * a⁻¹⁻¹) this
    simp only at this
    rw [@IsAssociative.assoc _ (· * ·), h2, h1] at this
    rw [@IsAssociative.assoc _ (· * ·), h2 a⁻¹, h1] at this
    exact this
  rw [h2, h1] at this
  rwa [← h2 a, @IsAssociative.assoc _ (· * ·)]

theorem hMul_left_inv (a : G) : a⁻¹ * a = 1 :=
  by
  calc
    a⁻¹ * a = a⁻¹ * a⁻¹⁻¹ := _
    _ = 1 := h2 a⁻¹
  apply congr_arg
  calc
    a = a * 1 := (h1 a).symm
    _ = a * (a⁻¹ * a⁻¹⁻¹) := by rw [h2]
    _ = a * a⁻¹ * a⁻¹⁻¹ := (IsAssociative.assoc a a⁻¹ a⁻¹⁻¹).symm
    _ = 1 * a⁻¹⁻¹ := by rw [h2]
    _ = a⁻¹⁻¹ := one_mul h1 h2 a⁻¹⁻¹

def ex112 : Group G :=
  { (by assumption : One G), (by assumption : Mul G),
    (by assumption : Inv G) with
    mul_assoc := IsAssociative.assoc
    hMul_left_inv := by convert mul_left_inv h1 h2
    one_mul := by convert one_mul h1 h2
    mul_one := h1 }

end Ex112

namespace Ex113

instance : Mul { z : ℂ // ‖z‖ = 1 } :=
  ⟨fun a b => ⟨a * b, by rw [norm_mul, a.prop, b.prop, one_mul]⟩⟩

theorem hMul_def (a b : { z : ℂ // ‖z‖ = 1 }) :
    a * b = ⟨a * b, by rw [norm_mul, a.prop, b.prop, one_mul]⟩ :=
  rfl

def hMul_assoc (a b c : { z : ℂ // ‖z‖ = 1 }) : a * b * c = a * (b * c) := by
  simp [mul_def, mul_assoc]

noncomputable instance : Inv { z : ℂ // ‖z‖ = 1 } :=
  ⟨fun a => ⟨a⁻¹, by rw [norm_inv, a.prop, inv_one]⟩⟩

theorem inv_def (a : { z : ℂ // ‖z‖ = 1 }) : a⁻¹ = ⟨a⁻¹, by rw [norm_inv, a.prop, inv_one]⟩ :=
  rfl

instance : One { z : ℂ // ‖z‖ = 1 } :=
  ⟨⟨1, norm_one⟩⟩

theorem one_def : (1 : { z : ℂ // ‖z‖ = 1 }) = ⟨1, norm_one⟩ :=
  rfl

noncomputable def ex113 : Group { z : ℂ // ‖z‖ = 1 }
    where
  mul := (· * ·)
  mul_assoc := hMul_assoc
  one := 1
  one_mul a := by simp [mul_def, one_def]
  mul_one a := by simp [mul_def, one_def]
  inv a := a⁻¹
  hMul_left_inv a :=
    by
    have : (a : ℂ) ≠ 0 := by rw [← norm_ne_zero_iff, a.prop]; exact one_ne_zero
    simp [mul_def, inv_def, inv_mul_cancel this, one_def]

/- ./././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(complex.exp «expr * »(θ, complex.I)) | θ : exprℝ()} -/
theorem ex1_1_3' :
    {z : ℂ | ‖z‖ = 1} =
      "./././Mathport/Syntax/Translate/Expr.lean:373:4: unsupported set replacement {(complex.exp «expr * »(θ, complex.I)) | θ : exprℝ()}" :=
  by
  ext z
  simp only [Complex.norm_eq_abs, Set.mem_setOf_eq, Complex.abs_eq_one_iff]

end Ex113
