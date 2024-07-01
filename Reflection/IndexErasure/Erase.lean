import Reflection.MInd

namespace Reflection.IndexErasure

set_option pp.fieldNotation.generalized false
open Reflection MInd
open Tyₛ Tyₚ Varₛ Varₚ

-- # Erasure

def eTyₛ : Tyₛ.{u} -> Tyₛ.{u}
| _ => U

/-- For example maps sort-ctx `[Vec : Nat -> U, ...]` into `[VecE : U, ...]`. -/
def eConₛ : Conₛ.{u} -> Conₛ.{u}
| ⬝      => ⬝
| Γₛ ▹ _ => eConₛ Γₛ ▹ U

/-- This is a no-op, other than changing the type of the variable. -/
def eVarₛ : Varₛ Γₛ Aₛ -> Varₛ (eConₛ Γₛ) U
| .vz   => .vz
| .vs v => .vs (eVarₛ v)

/-- For example maps `Vec : Nat -> U ⊢ Vec 123 : U` into `VecE : U ⊢ VecE : U`. -/
def eTmₛ : Tmₛ Γₛ Aₛ -> Tmₛ (eConₛ Γₛ) U
| .var v              => .var (eVarₛ v)
| .app (A := _Aₛ) t u => eTmₛ t

/-- For example for `Vec.nil`, maps `Vec : Nat -> U ⊢ Vec 0` into `VecE : U ⊢ VecE`,
and for `Vec.cons` maps `Vec : Nat -> U ⊢ (n:Nat) -> α -> Vec n -> Vec (n+1)`
into `VecE : U ⊢ (n:Nat) -> α -> VecE -> VecE`. -/
def eTyₚ {Γₛ : Conₛ} : Tyₚ Γₛ -> Tyₚ (eConₛ Γₛ)
| El         Self => El (eTmₛ Self)
| PPi   T    Rest => PPi T (fun t => eTyₚ (Rest t))
| PFunc Self Rest => PFunc (eTmₛ Self) (eTyₚ Rest)

def eConₚ : Conₚ Γₛ -> Conₚ (eConₛ Γₛ)
| ⬝ => ⬝
| Γ ▹ A => (eConₚ Γ) ▹ (eTyₚ A)

def eVarₚ : Varₚ Γ A -> Varₚ (eConₚ Γ) (eTyₚ A)
| .vz => .vz
| .vs v => .vs (eVarₚ v)

def eTmₚ : Tmₚ.{u, v} Γ A -> Tmₚ.{u, v} (eConₚ Γ) (eTyₚ A)
| .var v => .var (eVarₚ v)
| .app (A := _A) t u => .app (eTmₚ t) u
| .appr t u => .appr (eTmₚ t) (eTmₚ u)

abbrev ETyₛA Aₛ := TyₛA (eTyₛ Aₛ) -- actually this is a constant `ETyₛA := Type _`
abbrev EConₛA.{u, v} Γₛ := ConₛA.{u, v} (eConₛ Γₛ)
abbrev EVarₛ (Γₛ : Conₛ) : Type _ := Varₛ (eConₛ Γₛ) U
abbrev ETmₛ (Γₛ : Conₛ) : Type _ := Tmₛ (eConₛ Γₛ) U
abbrev ETmₛA.{u, v} (T : Tmₛ.{u} Γₛ Aₛ) (γₛE : EConₛA.{u, v} Γₛ) : Type _ := TmₛA.{u, v} (eTmₛ.{u} T) γₛE
abbrev mkETyₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₛ : Tyₛ} (t : Tmₛ Ωₛ Aₛ) : TyₛA.{u, u+1} U.{u} := mkTyₛ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ) (eTmₛ t)
abbrev mkEConₛ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : EConₛA.{u, u+1} Ωₛ                 := mkConₛ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ)

abbrev ETyₚ (Γₛ : Conₛ) : Type _ := Tyₚ (eConₛ Γₛ)
abbrev ETyₚA (A : Tyₚ Γₛ) (γₛE : EConₛA Γₛ) : Type _ := TyₚA (eTyₚ A) γₛE
abbrev EConₚ (Γₛ : Conₛ) : Type _ := Conₚ (eConₛ Γₛ)
abbrev EConₚA (Γ : Conₚ Γₛ) (γₛE : EConₛA Γₛ) : Type _ := ConₚA (eConₚ Γ) γₛE
abbrev EVarₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) : Type _ := Varₚ (eConₚ Γ) (eTyₚ A)
abbrev ETmₚ (Γ : Conₚ Γₛ) (A : Tyₚ Γₛ) : Type _ := Tmₚ (eConₚ Γ) (eTyₚ A)
abbrev mkETyₚ.{u} (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₚ : Tyₚ Ωₛ} (t : Tmₚ Ωₚ Aₚ) : ETyₚA Aₚ (mkEConₛ Ωₛ Ωₚ) := mkTyₚ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ) (eTmₚ t)
abbrev mkETyₚ_bad.{u} (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) {Aₚ : Tyₚ Ωₛ} (t : ETmₚ Ωₚ Aₚ) : ETyₚA Aₚ (mkEConₛ Ωₛ Ωₚ)
  := mkTyₚ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ) t
abbrev mkEConₚ (Ωₛ : Conₛ) (Ωₚ : Conₚ Ωₛ) : EConₚA.{u, u+1} Ωₚ (mkEConₛ Ωₛ Ωₚ) := mkConₚ.{u, u} (eConₛ Ωₛ) (eConₚ Ωₚ)

theorem mkEConₛ_coherent {t : Tmₛ Ωₛ Aₛ} : TmₛA (eTmₛ t) (mkEConₛ Ωₛ Ωₚ) = mkETyₛ Ωₛ Ωₚ t := by
  rw [mkEConₛ, mkETyₛ, mkConₛ]
  rw [mkConₛ_coherent]
  rw [SubₛTm_id]

theorem mkEConₚ_coherent {Ωₛ : Conₛ} {Ωₚ : Conₚ Ωₛ} {Aₚ : Tyₚ Ωₛ} {t : Tmₚ Ωₚ Aₚ}
  : TmₚA (eTmₚ t) (mkEConₚ Ωₛ Ωₚ) = mkETyₚ Ωₛ Ωₚ t
:= by rw [mkETyₚ, mkEConₚ, mkConₚ, mkConₚ_coherent, SubₚTm_id]

#check mkConₚ_coherent

#check @ETmₚ
theorem mkEConₚ_coherent_bad {Ωₛ : Conₛ} {Ωₚ : Conₚ Ωₛ} {Aₚ : Tyₚ Ωₛ} {t : ETmₚ Ωₚ Aₚ}
  -- @TmₚA (eConₛ Ωₛ) (eConₚ Ωₚ) (mkEConₛ Ωₛ Ωₚ) (eTyₚ Aₚ) t (mkEConₚ Ωₛ Ωₚ)
  : TmₚA t (mkEConₚ Ωₛ Ωₚ) = mkETyₚ_bad Ωₛ Ωₚ t
:= by rw [mkETyₚ_bad, mkEConₚ, mkConₚ, mkConₚ_coherent, SubₚTm_id]
