import Mathlib
import WeilRepFinitefield.Compute
import WeilRepFinitefield.WeilRep
import WeilRepFinitefield.Quadratictwo



open Matrix
local notation:max "M2" => Matrix (Fin 2) (Fin 2) (ZMod 2)


local notation:max "V2" => Matrix (Fin 2) (Fin 1) (ZMod 2)

abbrev B1 : M2 := !![0,1; 0,0]
abbrev v1 : V2 := !![0; 1]

abbrev χ : AddChar (ZMod 2) QQ where
  toFun := fun x => match x with
  | 0 => 1
  | 1 => -1
  map_zero_eq_one' := rfl
  map_add_eq_mul' := by
    intros a b;
    fin_cases a <;> fin_cases b
    all_goals native_decide


section Bilinear_Forms

variable (n : ℕ)

abbrev MM := Matrix (Fin (2*n)) (Fin (2*n)) (ZMod 2)

abbrev VV := Fin (2*n) → (ZMod 2)


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

namespace Witt_1

abbrev B0 : MM 1 := !![0, 1; 0, 0]



#eval FinEnum.toList $ QuadForm (ZMod 2) 2

-- Proposition 4.2 part 1
abbrev O2 :=  Finset.filter (is_orthogonal_transform B0)  (Finset.univ)

lemma O2.univ_eq : O2 = {!![0, 1; 1, 0], !![1, 0; 0, 1]}
  := by decide


end Witt_1

namespace Witt_0

abbrev B0 : MM 1 := !![1,1;0,1]
-- Proposition 4.5 part 1
#eval Finset.filter (is_orthogonal_transform B0)  (Finset.univ)

abbrev O2 :=  Finset.filter (is_orthogonal_transform B0)  (Finset.univ)

--#eval O2
-- Proposition 4.5 part 1
lemma O2.univ_eq : O2 =
  {!![0, 1; 1, 0], !![0, 1; 1, 1], !![1, 0; 0, 1],
   !![1, 0; 1, 1], !![1, 1; 0, 1], !![1, 1; 1, 0]}
  := by native_decide





end Witt_0
