import Mathlib


section

universe u


variable {α β γ : Type*} {R :Type u} [CommSemiring R]


section FinEnum

abbrev FinEnum.some (α : Type*) [h : FinEnum α] [Nonempty α]: α :=  h.equiv.symm ⟨0, by exact FinEnum.card_pos⟩


instance FinEnum.ofRange [DecidableEq β] [FinEnum α] (f :α → β ): FinEnum (Set.range f) := by
  have :(Set.rangeFactorization f).Surjective := by exact Set.surjective_onto_range
  apply FinEnum.ofSurjective _ this


instance (priority:=5000) instReprSubtype_decide{p : α → Prop} [DecidablePred p] [Repr α] : Repr (Subtype p) where
  reprPrec s prec := "⟨" ++ reprPrec s.val prec ++ ",by decide⟩"


instance : ∀ (n : ℕ) [NeZero n],  FinEnum (ZMod n)
  | 0, h => (h.ne _ rfl).elim
  | n + 1, _ => @FinEnum.fin (n+1)

instance  Matrix.instFinEnum [FinEnum α] [FinEnum β] [FinEnum γ] :
  FinEnum $ Matrix α β γ := by
  unfold Matrix
  infer_instance

variable {M N: Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [FinEnum M] (f : M →ₗ[R] N)

def LinearMap.range_range : range f ≃ Set.range (f : M → N) where
  toFun := fun a => ⟨a.1, by simp only [Subtype.coe_prop]⟩
  invFun := fun a => ⟨a, by simp only [SetLike.coe_mem]⟩
  left_inv := fun _ =>  rfl
  right_inv := fun _ => rfl

instance LinearMap.instFinEnum_range [DecidableEq N]
    : FinEnum (LinearMap.range f) := by
      refine FinEnum.ofEquiv _ (f.range_range)


instance  [FinEnum R] [CommSemiring R]  [FinEnum α] [FinEnum β] [DecidableEq α]
 :
  FinEnum $ (α → R) →ₗ[R] (β → R):=  @FinEnum.ofEquiv  (Matrix β α R) ((α → R) →ₗ[R] (β → R)) (Matrix.instFinEnum) (LinearMap.toMatrix'.toEquiv)



instance [Repr R]  : Repr ((Fin n → R) →ₗ[R] (Fin m → R)) where
  reprPrec := fun v _ => "(" ++ repr v.toMatrix'++").toLin'"


instance  [FinEnum R]  [FinEnum α] [DecidableEq α]
 :
  FinEnum $ LinearMap.BilinForm R (α → R) :=  @FinEnum.ofEquiv  (Matrix α α R) _ (Matrix.instFinEnum) (LinearMap.BilinForm.toMatrix'.toEquiv)


instance [Repr R]  : Repr (LinearMap.BilinForm R (Fin n → R)) where
  reprPrec := fun v _ => "(" ++ repr v.toMatrix'++").toBilin'"

end FinEnum

section GLSubgroup

variable {R M : Type*} [CommSemiring R]  [AddCommMonoid M] [Module R M] {p : (M ≃ₗ[R] M) → Prop }

local notation "G" => {σ : M ≃ₗ[R] M // p σ}

instance LinearEquiv.instSubtypeEquivLike : EquivLike G M M where
  coe e := e.1.toFun
  inv e:= e.1.invFun
  coe_injective' e1 e2 h _ := by
    apply Subtype.val_injective
    apply LinearEquiv.toLinearMap_injective (DFunLike.coe_injective h)
  left_inv _ := by
    apply LinearEquiv.left_inv
  right_inv _ := by
    apply LinearEquiv.right_inv


abbrev LinearEquiv.id [AddCommMonoid M] [Module R M] : M ≃ₗ[R] M := 1


namespace SubGL

variable [pclosed : Fact (∀ {a b}, p a → p b → p (b.trans a))]

instance instHMul: HMul G G G where
  hMul := fun a b =>  ⟨b.1.trans a.1, pclosed.out a.2 b.2⟩

variable (a b : {σ : M ≃ₗ[R] M // p σ})


lemma  mul_def : a * b =
  ⟨b.1.trans a.1, pclosed.out a.2 b.2⟩:= rfl


@[simp]
lemma map_mul (v : M): (a * b) v = a ( b v ) := by
  rw [mul_def]
  calc
  _ = (b.1.trans a.1 ) v := by rfl


instance instSemigroup : Semigroup G where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    rfl

variable [pone : Fact (p 1)]

instance hasOne: One G  where
  one := ⟨1, pone.out⟩

omit pclosed in
lemma One_def : (1 : G) = ⟨1, pone.out⟩  := rfl

omit pclosed in
@[simp]
lemma map_one (v : M): (1 : G) v = v := by rfl

instance instMulOneClass : MulOneClass (G) where
  one_mul := by
    intro a
    simp [mul_def]
    rfl
  mul_one := by
    intro a
    simp [mul_def]
    rfl


instance instMonoid : Monoid (G) where
  one_mul := one_mul
  mul_one := mul_one


variable [pinv : Fact (∀ {a}, p a → p a.symm)]

instance instGroup : Group G where
  inv := fun σ=> ⟨σ.1.symm, pinv.out σ.2⟩
  inv_mul_cancel := fun a => by
    simp only [mul_def,LinearEquiv.self_trans_symm]
    rfl



lemma inv_def: a⁻¹ = ⟨a.1.symm, pinv.out a.2⟩ := rfl

@[simp]
lemma self_of_map_inv_self : a⁻¹ (a v) = v := by
  simp only [← map_mul, inv_mul_cancel, map_one]

@[simp]
lemma self_of_map_self_inv : a (a⁻¹ v) = v := by
  simp only [← map_mul, mul_inv_cancel, map_one]

end SubGL

end GLSubgroup

section Inv

variable [Fintype n] [DecidableEq n] [CommRing α] [Inv α]
instance (priority := 1000) Matrix.inv_of_inv : Inv (Matrix n n α):=
  ⟨fun A => A.det⁻¹ • A.adjugate⟩

end Inv

--#synth Inv (MM 1)

--#eval B⁻¹

section GLNotation
variable [Field K] [FinEnum K]  [FinEnum α] [DecidableEq α]

--#synth FinEnum $ { g : Matrix α α K // g.det ≠ 0}

def LinearEquiv.toGL' : ((α → K) ≃ₗ[K] (α → K)) ≃  { g : Matrix α α K // g.det ≠ 0} where
  toFun := fun e => by
    refine ⟨e.toMatrix',?_⟩
    have H:= LinearEquiv.isUnit_det' e
    simp only [LinearMap.det_toMatrix']
    exact IsUnit.ne_zero H
  invFun := fun g => by
    apply g.1.toLinearEquiv'
    have : Invertible g.1.det := invertibleOfNonzero g.2
    apply Matrix.invertibleOfDetInvertible
  left_inv := by
    intro g
    simp only [ne_eq, id_eq, eq_mpr_eq_cast, ← toLinearMap_inj, Matrix.toLinearEquiv'_apply,
      Matrix.toLin'_toMatrix']
  right_inv := by
    intro g
    simp only [ne_eq, Matrix.toLinearEquiv'_apply, LinearMap.toMatrix'_toLin', Subtype.coe_eta]

instance :  FinEnum $ (α → K) ≃ₗ[K] (α → K) :=  FinEnum.ofEquiv  ({ g : Matrix α α K // g.det ≠ 0})  (LinearEquiv.toGL')


instance : Inhabited ((α → K) ≃ₗ[K] (α → K)) where
  default := LinearEquiv.id


abbrev Matrix.toGL' : Matrix α α K → ((α → K) ≃ₗ[K] (α → K))
  := fun A => if H : A.det ≠ 0 then LinearEquiv.toGL'.symm ⟨A, H⟩ else default

syntax (name := GLNotation) "!GL" term  : term

macro_rules
  | `(!GL $term:term) => `(Matrix.toGL' $term )


@[app_unexpander Matrix.toGL']
def quadSnocUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ) => `(!GL $term)
  | _ => throw ()


instance instReprGL {n : ℕ} [Repr K]   : Repr ((Fin n → K) ≃ₗ[K] (Fin n → K))  where
  reprPrec := fun v _ => "!GL" ++ repr v.toGL'.1 ++ ""



end GLNotation

section HRadical

class HRadical {R : Type*} [Semiring R] (n :ℕ) (a : R) where
  r : R
  hr : r ^ n = a

/--
The following program compute √ |α| if |α| is a b0 power, with a fixed choice of √ b0
-/
abbrev sqrtrank {R : Type*} [Semiring R] (b0 : ℕ) (α : Type*) [Fintype α] [hb0 : HRadical 2 (b0:R)] : R := hb0.r ^ (Nat.log b0 (Fintype.card α))


end HRadical

/-
namespace Compute.test

local notation "F" => (ZMod 2)

abbrev MM n := Matrix (Fin (2*n)) (Fin (2*n)) (ZMod 2)
abbrev VV n := Fin (2*n) → (ZMod 2)

abbrev V2 := VV 1

local notation "GL2" => ((Fin 2) → F) ≃ₗ[F] ((Fin 2) → F)

abbrev AA := (!GL !![0,1;1,0]:GL2)
example : AA = AA := by
  rewrite [AA]
  rfl

#eval (Matrix.toGL' !![0, 1; 1, 0]:GL2)

#eval FinEnum.toList $ GL2

example : (FinEnum.toList $ GL2) =
  [!GL!![0, 1; 1, 0], !GL!![0, 1; 1, 1], !GL!![1, 0; 0, 1], !GL!![1, 0; 1, 1], !GL!![1, 1; 0, 1], !GL!![1, 1; 1, 0]]
  := by decide

abbrev B : MM 1 := !![0,1;1,1]

#eval B⁻¹

#eval (LinearEquiv.toGL'.symm ⟨!![0, 1; 1, 0],by decide⟩ : GL2)
#eval FinEnum.toList (Matrix (Fin 2) (Fin 2) F)
#eval FinEnum.toList (V2 →ₗ[F]V2)

example : FinEnum.toList (V2 →ₗ[F]V2) =[!![0, 0; 0, 0].toLin',
 !![0, 0; 0, 1].toLin',
 !![0, 0; 1, 0].toLin',
 !![0, 0; 1, 1].toLin',
 !![0, 1; 0, 0].toLin',
 !![0, 1; 0, 1].toLin',
 !![0, 1; 1, 0].toLin',
 !![0, 1; 1, 1].toLin',
 !![1, 0; 0, 0].toLin',
 !![1, 0; 0, 1].toLin',
 !![1, 0; 1, 0].toLin',
 !![1, 0; 1, 1].toLin',
 !![1, 1; 0, 0].toLin',
 !![1, 1; 0, 1].toLin',
 !![1, 1; 1, 0].toLin',
 !![1, 1; 1, 1].toLin'] := by decide

abbrev m :=  (!GL !![0, 1; 1, 0]:GL2).1

#check m

#eval  m.toMatrix'.trace

#eval FinEnum.toList ((Fin 2→ F) →ₗ[F](Fin 2 → F))


#eval FinEnum.toList (LinearMap.BilinForm F V2)

example : FinEnum.toList (LinearMap.BilinForm F V2)= [(!![0, 0; 0, 0]).toBilin',
 (!![0, 0; 0, 1]).toBilin',
 (!![0, 0; 1, 0]).toBilin',
 (!![0, 0; 1, 1]).toBilin',
 (!![0, 1; 0, 0]).toBilin',
 (!![0, 1; 0, 1]).toBilin',
 (!![0, 1; 1, 0]).toBilin',
 (!![0, 1; 1, 1]).toBilin',
 (!![1, 0; 0, 0]).toBilin',
 (!![1, 0; 0, 1]).toBilin',
 (!![1, 0; 1, 0]).toBilin',
 (!![1, 0; 1, 1]).toBilin',
 (!![1, 1; 0, 0]).toBilin',
 (!![1, 1; 0, 1]).toBilin',
 (!![1, 1; 1, 0]).toBilin',
 (!![1, 1; 1, 1]).toBilin']
 := by decide

end Compute.test
-/

end
