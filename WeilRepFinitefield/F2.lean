import Mathlib
import WeilRepFinitefield.QuadForm


open Matrix
local notation:max "M2" => Matrix (Fin 2) (Fin 2) (ZMod 2)


local notation:max "V2" => Matrix (Fin 2) (Fin 1) (ZMod 2)

abbrev B1 : M2 := !![0,1; 0,0]
abbrev v1 : V2 := !![0; 1]

/-
#eval B1 * v1
#eval v1.transpose * B1 * v1
#eval B1
#eval B1 * B1
instance aa: DecidableEq (Fin 2 → ZMod 2) := by infer_instance
instance aa': DecidableEq M2 := by infer_instance
-/

abbrev χ : (ZMod 2) → ℚ := fun x => match x with
  | 0 => 1
  | 1 => -1

/-
@[simp]
lemma Matrix.transpose_fin_two {a b c d: α} : !![a,b;c,d].transpose =!![a,c;b,d] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp

example (a b c d: R) [CommRing R] : !![a,b;c,d].transpose * !![0,1;-1,0] * !![a,b;c,d] = !![0,a*d-b*c; b*c - a*d, 0] := by
  rw  [Matrix.transpose_fin_two,Matrix.mul_fin_two,Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals ring_nf
-/


section Bilinear_Forms

variable (n : ℕ)

abbrev MM := Matrix (Fin (2*n)) (Fin (2*n)) (ZMod 2)

abbrev VV := Fin (2*n) → (ZMod 2)

abbrev QQ := QuadForm (ZMod 2) (2*n)

abbrev J : MM n := fun i j =>
  if j = n+i then 1 else if i = n+j then -1 else 0

abbrev Omega : M2 := J 1

#eval Omega

abbrev Sp : Finset (MM n) := Finset.filter (fun g =>  g.transpose * (J n) * g = (J n)) (Finset.univ)

namespace Sp2

-- Proposition 4.1 part 2
lemma univ_eq : Sp 1 = {
  !![0, 1; 1, 0], !![0, 1; 1, 1], !![1, 0; 0, 1],
  !![1, 0; 1, 1], !![1, 1; 0, 1], !![1, 1; 1, 0]}
  := by decide


end Sp2

abbrev is_form_J (B : MM n) : Prop :=
   (B -  B.transpose) = J n

abbrev all_B_forms : Finset (MM n) :=
Finset.filter (is_form_J n) (Finset.univ)

lemma all_bilinearforms : all_B_forms 1=
  {!![0, 0; 1, 0], !![0, 0; 1, 1], !![0, 1; 0, 0],
 !![0, 1; 0, 1], !![1, 0; 1, 0], !![1, 0; 1, 1],
 !![1, 1; 0, 0], !![1, 1; 0, 1]}
 := by decide

variable {n}
abbrev quadratic_form (B : MM n) : VV n → ZMod 2:= fun x =>
 (x ⬝ᵥ (B *ᵥ x))


abbrev is_orthogonal_transform (B : MM n) : MM n → Prop := fun g =>
  ∀ x : VV n, quadratic_form B x = quadratic_form B (g *ᵥ x)


def nilcone_card (B : MM n) : ℕ :=
  let nil := Finset.filter (fun x => quadratic_form B x= 0) (Finset.univ : Finset $ VV n)
  Finset.card nil

variable (B : MM n)

#eval (Finset.univ : Finset (MM 1 × QQ 1))

def Ps : Finset (MM n × QQ n) :=
Finset.filter
  (fun (σ,f) => ∀ w1 w2 : VV n, f.eval (w1+w2) - f.eval w1 - f.eval w2 = (σ *ᵥ w1) ⬝ᵥ (B *ᵥ (σ *ᵥ w2)) - w1 ⬝ᵥ B *ᵥ w2 )
  Finset.univ



namespace Witt_1

abbrev B0 : MM 1 := !![0, 1; 0, 0]


-- Proposition 4.2 part 1
abbrev O2 :=  Finset.filter (is_orthogonal_transform B0)  (Finset.univ)

lemma O2.univ_eq : O2 = {!![0, 1; 1, 0], !![1, 0; 0, 1]}
  := by decide

lemma Ps2.univ_eq : Ps B0 =
{(!![0, 1; 1, 0], !#[![0], ![1, 0]]),
 (!![0, 1; 1, 0], !#[![0], ![1, 1]]),
 (!![0, 1; 1, 0], !#[![1], ![1, 0]]),
 (!![0, 1; 1, 0], !#[![1], ![1, 1]]),
 (!![1, 0; 0, 1], !#[![0], ![0, 0]]),
 (!![1, 0; 0, 1], !#[![0], ![0, 1]]),
 (!![1, 0; 0, 1], !#[![1], ![0, 0]]),
 (!![1, 0; 0, 1], !#[![1], ![0, 1]])}
 := by native_decide

end Witt_1

namespace Witt_0

abbrev B0 : MM 1 := !![1,1;0,1]
-- Proposition 4.5 part 1
#eval Finset.filter (is_orthogonal_transform B0)  (Finset.univ)



#eval all_B_forms

end Witt_0
