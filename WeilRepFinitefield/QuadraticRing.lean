import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.Sqrt

/-!
# 可计算二次扩张环

以坐标对表示 R[√d]，建立加法、乘法等环运算；
在底环为域且 d 非平方的假设下构造域结构，为有限例子的精确系数计算提供支持。
-/

variable {R: Type*}
variable [CommRing R]

structure QuadraticRing (d : R) where
  a : R
  b : R

--def QuadraticRing (d : R) := R × R

namespace QuadraticRing
variable {d:R}

local notation:max "Q" => QuadraticRing d

abbrev toQring (d a b : R) : QuadraticRing d := ⟨a,b⟩


instance instDecidableEq [DecidableEq R] : DecidableEq (QuadraticRing d) := fun a b =>
  by
    rw [mk.injEq]
    infer_instance


instance instRepr [DecidableEq R] [Repr R]: Repr (QuadraticRing d) where
  reprPrec v _ :=
    if v.1 = 0 then
      if v.2=0  then "0"
      else repr v.2 ++ " √ " ++ repr d
    else
      if v.2=0 then repr v.1
      else "(" ++ repr v.1 ++ " + "++repr v.2 ++ " √ " ++ repr d ++ ")"

abbrev add : Q → Q → Q :=
  fun ⟨x,y⟩  ⟨z,w⟩  => ⟨x + z, y+w⟩


abbrev mul : Q → Q → Q :=
  fun ⟨x,y⟩  ⟨z,w⟩  => ⟨ x * z + d* y *w, x*w+ y*z⟩

instance instHAdd : HAdd Q Q Q where
  hAdd := add


@[simp]
lemma add_def {a b :Q} : a+b = ⟨a.1 + b.1, a.2 + b.2⟩  := rfl

instance withZero : Zero Q where
  zero := ⟨0,0⟩

@[simp]
lemma zero_def : (0 : Q) = ⟨0,0⟩  := rfl

@[simp]
lemma zero_def1 : (0 : Q).1 =0 := rfl

@[simp]
lemma zero_def2 : (0 : Q).2 =0 := rfl


instance instAddCommMonoid : AddCommMonoid $ QuadraticRing d where
    add := add
    add_assoc := by
      intro a b c
      simp only [add_def, mk.injEq]
      constructor<;>ring_nf
    zero_add := by
      intro a
      simp only [zero_def, add_def, zero_add]
    add_zero := by
      intro a
      simp only [zero_def, add_def, add_zero]
    nsmul := fun n ⟨a,b⟩ => ⟨n*a, n*b⟩
    nsmul_succ := by
      intro n ⟨a,b⟩
      simp only [Nat.cast_add, Nat.cast_one, add_def, mk.injEq]
      constructor <;> ring_nf
    nsmul_zero := by
      intro n
      simp only [Nat.cast_zero, zero_mul, zero_def]
    add_comm := by
      intro a b
      simp [add_def,add_comm]


instance instAddCommGroup : AddCommGroup $ QuadraticRing d :=
   {
    instAddCommMonoid with
    neg := fun ⟨a,b⟩ => ⟨-a,-b⟩
    zsmul := fun n ⟨a,b⟩ => ⟨n*a, n*b⟩
    zsmul_zero' :=  by simp
    zsmul_succ' := by
      intro a n
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast,
        Int.cast_one, add_def, mk.injEq]
      constructor <;> ring_nf
    zsmul_neg' := by
      intro n a
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, Nat.succ_eq_add_one,
        Int.cast_add, Int.cast_natCast, Int.cast_one, mk.injEq]
      constructor <;> ring_nf
    neg_add_cancel := by
      intro a
      simp only [add_def, neg_add_cancel, zero_def]
   }

@[simp]
lemma neg_def {a :QuadraticRing d} : -a = ⟨-a.1,-a.2⟩  := rfl


@[simp]
lemma neg_def' {a b : R} : -(⟨a,b⟩:QuadraticRing d)  = ⟨-a,-b⟩  := rfl


instance instHMul : HMul (QuadraticRing d) (QuadraticRing d) (QuadraticRing d) where
  hMul := mul

@[simp]
lemma mul_def {a b :Q} : a*b = ⟨a.1 * b.1 + d*a.2 *b.2, a.1*b.2 + a.2*b.1⟩ := rfl

instance withOne : One Q where
  one := ⟨1,0⟩

@[simp]
lemma one_def : (1 : Q) = ⟨1,0⟩  := rfl

@[simp]
lemma one_def1 : (1 : Q).1 =1 := rfl

@[simp]
lemma one_def2 : (1 : Q).2 =0 := rfl




instance instCommMonoid : CommMonoid Q where
  mul := mul
  mul_assoc := by
    intro a b c
    simp only [mul_def]
    ring_nf
  one_mul := by
    intro a
    simp only [mul_def, one_def1, one_mul, one_def2, mul_zero, zero_mul, add_zero, Prod.mk.eta]
  mul_one := by intro a; simp
  mul_comm := by
    intro a b
    rw [mul_def,mul_def]
    ring_nf

instance instRing : Ring Q :=
  {instCommMonoid,instAddCommGroup with
    left_distrib := by
      intro a b c
      simp only [add_def, mul_def]
      ring_nf
    right_distrib := by
      intro a b c
      simp only [add_def, mul_def]
      ring_nf
    zero_mul := by
      intro a
      simp only [add_def, mul_def,zero_def]
      ring_nf
    mul_zero := by
      intro a
      simp only [add_def, mul_def,zero_def]
      ring_nf
  }

instance instCommRing: CommRing Q := {instRing,instCommMonoid with }


/-- A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory. -/
class Nonsquare (x : R) : Prop where
  ns' : ∀ n : R, x ≠ n * n

@[simp]
theorem Nonsquare.ns (x : R) [h: Nonsquare x] : ∀ n : R, x ≠ n * n := ns'


instance field_is_domain {F : Type*} [Field F]: IsDomain F := inferInstance

instance field_no_zero_divisors [Field F]: NoZeroDivisors F := by
  constructor; intro a b hab
  by_contra H
  push_neg at H
  apply H.2
  apply_fun (a⁻¹ * · ) at hab
  rw [mul_zero,<-mul_assoc,mul_comm _ a,DivisionRing.mul_inv_cancel _ H.1] at hab
  rw [<-hab,one_mul]

theorem divides_sq_eq_zero {R:Type*}  [Field R] {d : R} [h: Nonsquare d]: ∀ {x y : R}, x * x = d * y * y ↔ x = 0 ∧ y =0:= by
  intro x y
  constructor
  · intro H
    by_contra HH
    rw [not_and_or] at HH
    wlog H2 : y ≠ 0 with HWLOG
    rcases HH with HH | HH
    · push_neg at H2
      rw [H2] at H
      replace H : x*x = 0 := by simp [H]
      apply HH
      rw [<-@mul_self_eq_zero _ _ (field_no_zero_divisors (F:=R)) ,H]
    · apply H2
      exact HH
    apply_fun ( · * y⁻¹ * y⁻¹ ) at H
    rw [mul_assoc _ y y⁻¹ , DivisionRing.mul_inv_cancel _ H2,mul_one] at H
    rw [mul_assoc _ y y⁻¹ , DivisionRing.mul_inv_cancel _ H2,mul_one] at H
    replace h:= Nonsquare.ns d
    specialize h (x* y⁻¹)
    apply h
    rw [<-H]
    ring
  · rintro ⟨hx,hy⟩
    simp [hx,hy]

end QuadraticRing

section QuadraticField

variable {F : Type*} [Field F] (d:F)

abbrev QuadraticField := QuadraticRing d

namespace QuadraticField
open QuadraticRing

instance instInv : Inv (QuadraticField d) where
  inv := fun ⟨a,b⟩ => ⟨a / (a*a - d*b*b), -b/(a*a - d*b*b)⟩

@[simp]
lemma inv_def {a : QuadraticField d} : a⁻¹ = ⟨a.1 / (a.1*a.1 - d*a.2*a.2), -a.2/(a.1*a.1 - d*a.2*a.2)⟩ := rfl


@[simp]
lemma inv_def' {a b: F} : (⟨a,b⟩ :QuadraticField d) ⁻¹ = ⟨a / (a*a - d*b*b), -b/(a*a - d*b*b)⟩ := rfl



variable [Nonsquare d]

/-
instance instDivisionRing: DivisionRing (QuadraticField d)  where
-/

instance instField: Field (QuadraticField d) where
  exists_pair_ne := by
    use 0, 1; simp
  mul_inv_cancel := by
    intro ⟨a,b⟩  ha
    have H : ¬ (a = 0  ∧  b = 0) := by
      intro ⟨h1,h2⟩; rw [h1,h2] at ha; contradiction
    have H : a*a - d * b * b ≠ 0:= by
      intro H'
      replace H' : a *a  = d * b *b := eq_of_sub_eq_zero H'
      rw [QuadraticRing.divides_sq_eq_zero] at H'
      exact H H'
    simp only [inv_def, mul_def, one_def, mk.injEq]
    constructor
    · field_simp [H]
      ring_nf
    · field_simp [H]
      ring_nf
  inv_zero := by simp only [zero_def, inv_def, mul_zero, sub_self, div_zero, neg_zero]
  nnqsmul := _
  qsmul := _


end QuadraticField

end QuadraticField
