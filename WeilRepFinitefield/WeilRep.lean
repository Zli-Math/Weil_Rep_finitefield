import Mathlib
import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.PseudoSymplecticGroup

open Module
open BigOperators
open Heisenberg pseudo_symplectic symplectic

variable {K : Type } [Field K] [Fintype K] {V : Type } [Fintype V] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable (B : V → V → K) [IsBilinear B]
variable [hnd : NonDegenerate (alternatingform B)]


variable {X Y : Submodule K V} (χ₀ : AddChar K ℂˣ) (hp : polarization B X Y)

variable (χ : (subXK B (X := X)) →* ℂˣ) [isextendchara : extendcharacter B χ₀ χ]

variable (s : symplectic_automorphism B)
variable (w : V)

noncomputable section

local notation "ρ" => (rhoY hp χ)


def omega_aux : End ℂ (Ymodel hp) :=
  ∑ (v : V) , ((ρ (s v : Heisenberg B)⁻¹).comp (ρ (w))).comp (ρ v)




end
