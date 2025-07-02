import Mathlib.RingTheory.Algebraic.Basic

variable {R: Type*}
variable [CommRing R]

def QuadraticRing (d : R) := R×R

namespace QuadraticRing
variable {d:R}

local notation:max "Q" => QuadraticRing d

abbrev add : Q → Q → Q :=
  fun (x,y) (z,w) => (x + z, y+w)


abbrev mul : Q → Q → Q :=
  fun (x,y) (z,w) => (x * z + d* y *w, x*w+ y*z)

instance hAdd : HAdd Q Q Q where
  hAdd := add

@[simp]
lemma add_def {a b :Q} : a+b = (a.1 + b.1, a.2 + b.2) := rfl

instance hMul : HMul Q Q Q where
  hMul := mul

@[simp]
lemma mul_def {a b :Q} : a*b = (a.1 * b.1 + d*a.2 *b.2, a.1*b.2 + a.2*b.1) := rfl

instance withOne : One Q where
  one := (1,0)

@[simp]
lemma one_def1 : (1 : Q).1 =1 := rfl

@[simp]
lemma one_def2 : (1 : Q).2 =0 := rfl

instance withZero : Zero Q where
  zero := (0,0)

@[simp]
lemma zero_def1 : (0 : Q).1 =0 := rfl

@[simp]
lemma zero_def2 : (0 : Q).2 =0 := rfl


instance instCommRing : Monoid Q where
  mul := mul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    ring_nf
  one_mul := by
    intro a
    simp [mul_def]
  mul_one := by intro a; simp



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

section

local notation:max "Q" => QuadraticRing (2 : ℚ)



end
