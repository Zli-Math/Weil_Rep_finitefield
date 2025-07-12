import Mathlib
import WeilRepFinitefield.Compute
import WeilRepFinitefield.WeilRep
import WeilRepFinitefield.Quadratictwo

set_option quotPrecheck false

open Matrix LinearMap

local notation "K" => (ZMod 2)

abbrev MM n := Matrix (Fin (2*n)) (Fin (2*n)) (ZMod 2)
abbrev VV n := Fin (2*n) → (ZMod 2)

variable {n} in
abbrev projX : VV n →ₗ[K] VV n where
  toFun := fun a => (fun i => if i < n then a i else 0)
  map_add' := by
    intro x y
    ext i
    by_cases h : i < n <;> simp [h]
  map_smul' := by
    intro a x
    ext i
    by_cases h : i < n <;> simp [h]


variable {n} in
abbrev embedX : (Fin n → K) →ₗ[K] VV n where
  toFun := fun a => (fun i => if hi:i < n then a ⟨i,hi⟩  else 0)
  map_add' := by
    intro x y
    ext i
    by_cases h : i < n <;> simp [h]
  map_smul' := by
    intro a x
    ext i
    by_cases h : i < n <;> simp [h]

variable {n} in
abbrev embedY : (Fin n → K) →ₗ[K] VV n where
  toFun := fun a => (fun i => if hi:i >= n then a ⟨i-n,by
    refine Nat.sub_lt_left_of_lt_add hi ?_
    linarith [i.2]
  ⟩
  else 0)
  map_add' := by
    intro x y
    ext i
    by_cases h : i >= n <;> simp [h]
  map_smul' := by
    intro a x
    ext i
    by_cases h : i >= n <;> simp [h]

variable {n} in
abbrev projY : VV n →ₗ[K] VV n where
  toFun := fun a => (fun i => if i < n then 0 else a i)
  map_add' := by
    intro x y
    ext i
    by_cases h : i < n <;> simp [h]
  map_smul' := by
    intro a x
    ext i
    by_cases h : i < n <;> simp [h]

abbrev XX n := LinearMap.range <| projX (n:=n)
abbrev YY n := LinearMap.range <| projY (n:=n)

abbrev BBmat n: MM n := fun i j => if i < n ∧ j = n+i then 1 else 0
abbrev BB n : LinearMap.BilinForm K (VV n) := BBmat n |>.toBilin'

def PP n  : (BB n).Polarization (XX n) (YY n) where
  iota := {
    toFun := fun ⟨a,b⟩ => a +b
    map_add' := sorry
    map_smul' := sorry
    invFun := fun v => ((projX.rangeRestrict v), (projY.rangeRestrict v))
    left_inv := sorry
    right_inv := sorry
  }
  embed := sorry
  Xisotropic := sorry
  Yisotropic := sorry


abbrev χ : AddChar (ZMod 2) QQ where
  toFun := fun x => match x with
  | 0 => 1
  | 1 => -1
  map_zero_eq_one' := rfl
  map_add_eq_mul' := by
    intros a b;
    fin_cases a <;> fin_cases b
    all_goals native_decide

abbrev χ' : AddChar (ZMod 2) QQˣ where
  toFun := fun x => match x with
  | 0 => 1
  | 1 => -1
  map_zero_eq_one' := rfl
  map_add_eq_mul' := by
    intros a b;
    fin_cases a <;> fin_cases b
    all_goals native_decide

def tchi : ((BB n).toSubgroup (XX n)) →* QQˣ where
  toFun := fun ⟨⟨a,b⟩,_⟩ => χ' b
  map_one' := rfl
  map_mul' := by sorry


#synth FinEnum (YY 2)


abbrev M2 := MM 1
abbrev V2 := VV 1
abbrev P2 := PP 1

local notation "GL2" => ((Fin 2) → K) ≃ₗ[K] ((Fin 2) → K)
local notation "QF2" => QuadraticForm K n

abbrev B1mat : M2 := !![0,1; 0,0]
abbrev B : LinearMap.BilinForm K V2 := B1mat.toBilin'




#eval FinEnum.toList <| B.Sp

--#eval!  FinEnum.toList <| B.Ps
-- Result of #eval! which lists all elements in B.Ps
def all_ps :List (B.Ps) :=
[⟨(!GL!![0, 1; 1, 0], (!QF !![0, 0; 1, 0]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![0, 1; 1, 0], (!QF !![0, 0; 1, 1]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![0, 1; 1, 0], (!QF !![1, 0; 1, 0]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![0, 1; 1, 0], (!QF !![1, 0; 1, 1]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![1, 0; 0, 1], (!QF !![0, 0; 0, 0]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![1, 0; 0, 1], (!QF !![0, 0; 0, 1]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![1, 0; 0, 1], (!QF !![1, 0; 0, 0]).toQuadraticForm),by decide⟩,
 ⟨(!GL!![1, 0; 0, 1], (!QF !![1, 0; 0, 1]).toQuadraticForm),by decide⟩]


#eval! all_ps

def s1 := all_ps[0]
def s2 := all_ps[1]
def s3 := all_ps[2]
def s4 := all_ps[3]
def s5 := all_ps[4]
def s6 := all_ps[5]
def s7 := all_ps[6]
def s8 := all_ps[7]

#eval! P2.cocycle tchi s1 s2

def matrixcocycle' (ls : List B.Ps):=
  let n := ls.length
  Matrix.of (fun (i : Fin n) (j : Fin n)=> ls[i].cocycle' χ ls[j])


def matrixcocycle (ls : List B.Ps):=
  let n := ls.length
  Matrix.of (fun (i : Fin n) (j : Fin n)=> P2.cocycle tchi ls[i] ls[j])

#eval! matrixcocycle all_ps

#eval! matrixcocycle' all_ps

#eval! s1.cocycle' χ s2
#eval! s5.cocycle' χ s4
