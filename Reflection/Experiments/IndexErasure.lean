import Reflection.MutualInductive

open Tyₛ Tyₚ Varₛ Varₚ

-- # Erasure

def eraseTyₛ : Tyₛ.{u} -> Tyₛ.{u}
| _ => U

/-- For example maps sort-ctx `[Vec : Nat -> U, ...]` into `[VecE : U, ...]`. -/
def eraseConₛ : Conₛ.{u} -> Conₛ.{u}
| ⬝      => ⬝
| Γₛ ▹ _ => eraseConₛ Γₛ ▹ U

/-- This is a no-op, other than changing the type of the variable. -/
def eraseVarₛ : Varₛ Γₛ Aₛ -> Varₛ (eraseConₛ Γₛ) U
| .vz   => .vz
| .vs v => .vs (eraseVarₛ v)

/-- For example maps `Vec : Nat -> U ⊢ Vec 123 : U` into `VecE : U ⊢ VecE : U`. -/
def eraseTmₛ : Tmₛ Γₛ Aₛ -> Tmₛ (eraseConₛ Γₛ) U
| .var v              => .var (eraseVarₛ v)
| .app (A := _Aₛ) t u => eraseTmₛ t

/-- For example for `Vec.nil`, maps `Vec : Nat -> U ⊢ Vec 0` into `VecE : U ⊢ VecE`,
and for `Vec.cons` maps `Vec : Nat -> U ⊢ (n:Nat) -> α -> Vec n -> Vec (n+1)`
into `VecE : U ⊢ (n:Nat) -> α -> VecE -> VecE`. -/
def eraseTyₚ {Γₛ : Conₛ} : Tyₚ Γₛ -> Tyₚ (eraseConₛ Γₛ)
| El         Self => El (eraseTmₛ Self)
| PPi   T    Rest => PPi T (fun t => eraseTyₚ (Rest t))
| PFunc Self Rest => PFunc (eraseTmₛ Self) (eraseTyₚ Rest)

def eraseConₚ : Conₚ Γₛ -> Conₚ (eraseConₛ Γₛ)
| ⬝ => ⬝
| Γ ▹ A => (eraseConₚ Γ) ▹ (eraseTyₚ A)

def eraseVarₚ : Varₚ Γ A -> Varₚ (eraseConₚ Γ) (eraseTyₚ A)
| .vz => .vz
| .vs v => .vs (eraseVarₚ v)

def eraseTmₚ : Tmₚ Γ A -> Tmₚ (eraseConₚ Γ) (eraseTyₚ A)
| .var v => .var (eraseVarₚ v)
| .app (A := _A) t u => .app (eraseTmₚ t) u
| .appr t u => .appr (eraseTmₚ t) (eraseTmₚ u)

-- # Guard

/-- For example maps `Vec : Nat -> U` to `VecG : Nat -> VecE -> U`.
  Note that `∀Aₛ, TyₛA (eraseTyₛ Aₛ) = Type`. -/
-- def guardTyₛ : (Aₛ : Tyₛ.{u}) -> TyₛA.{u, u} (eraseTyₛ Aₛ) -> Tyₛ.{u}
def guardTyₛ : (Aₛ : Tyₛ.{u}) -> Type u -> Tyₛ.{u}
| U         , aₛE => SPi aₛE (fun _ => U)
| SPi T Rest, aₛE => SPi T   (fun t => guardTyₛ (Rest t) aₛE)

/-- For example maps sort-stx `[Vec : Nat -> U]` into `[VecG : Nat -> VecE -> U]`. -/
def guardConₛ.{u} : (Γₛ : Conₛ.{u}) -> (γₛE : ConₛA.{u, u} (eraseConₛ Γₛ)) -> Conₛ.{u}
| ⬝      , ⟨⟩         => ⬝
| Γₛ ▹ Aₛ, ⟨γₛE, aₛE⟩ => Conₛ.ext (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ aₛE)

/-- Given a variable `Vec:N->U ⊢ VAR(Vec) : N->U`, we return `VecG:N->VecE->U ⊢ VAR(VecG) : N->VecE->U`.
  The runtime de-brujin value of this variable doesn't change. So this is basically just a cast operator. -/
def guardVarₛ : {Γₛ : Conₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) ->
  (v : Varₛ Γₛ Aₛ) ->
  Varₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ (VarₛA (eraseVarₛ v) γₛE))
| _ ▹ _, _       , .vz   => .vz
| _ ▹ _, ⟨γₛE, _⟩, .vs v => .vs (guardVarₛ γₛE v)


/-- Given `Γₛ ⊢ Self a₁ a₂ a₃ : U` returns `guard(Γₛ) ⊢ SelfG a₁ a₂ a₃ : SelfE -> U`.

  Challange is that we don't know which type (`Even`, `Odd`, etc) `t` refers to,
  it could be `Even @ 123` or `Odd @ 123`.
  So the output term's type needs to depend on `t`.  -/
def guardTmₛ : {Γₛ : Conₛ.{u}} -> (γₛE : ConₛA.{u, u} (eraseConₛ Γₛ)) ->
  (t : Tmₛ.{u} Γₛ Aₛ) ->
  Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ (TmₛA (eraseTmₛ t) γₛE))
| Γₛ, γₛE, .var v              => by
  rw [eraseTmₛ, TmₛA]
  exact .var (guardVarₛ.{u, u} γₛE v)
| Γₛ, γₛE, .app (A := _Aₛ) t u => .app (guardTmₛ γₛE t) u

/-- For example maps the `Vec.cons` ctor of type
```
Vec : Nat ->          U ⊢ (n:Nat) -> (_:A) -> (_ : Vec n) ->            Vec (n+1)
```
into `VecG.cons` of type
```
VecG : Nat -> VecE -> U ⊢ (n:Nat) -> (x:A) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons (n+1) x e)
``` -/
def guardTyₚ.{u} (γₛE : ConₛA.{u} (eraseConₛ Γₛ)) : (A : Tyₚ Γₛ) -> (aE : TyₚA.{u, u} (eraseTyₚ A) γₛE) ->
  Tyₚ (guardConₛ Γₛ γₛE)
| El         Self, aE => El (.app (guardTmₛ γₛE Self) aE) -- VecG ... (VecE.cons ...)
| PPi   T    Rest, aE => PPi T (fun t => guardTyₚ γₛE (Rest t) (aE t))
| PFunc Self Rest, aE => -- this `Self` could be from a different ind type from the mutual block!
    PPi (TmₛA (eraseTmₛ Self) γₛE) fun e =>  -- (e : SelfE) ->
      PFunc (.app (guardTmₛ γₛE Self) e) <| -- SelfG e ->
        guardTyₚ γₛE Rest (aE e)

def guardConₚ (γₛE : ConₛA (eraseConₛ Γₛ)) : (Γ : Conₚ Γₛ) -> (γE : ConₚA (eraseConₚ Γ) γₛE) -> Conₚ (guardConₛ Γₛ γₛE)
| ⬝, ⟨⟩ => ⬝
| Γ ▹ A, ⟨γE, aE⟩ => guardConₚ γₛE Γ γE ▹ guardTyₚ γₛE A aE


/-- Cast `"Vec.cons"` to `"VecG.cons"`, similar to `guardTmₚ`. -/
def guardVarₚ : {Γ : Conₚ Γₛ} -> (γₛE : ConₛA (eraseConₛ Γₛ)) -> (γE : ConₚA (eraseConₚ Γ) γₛE) ->
  (v : Varₚ Γ A) ->
  Varₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA (.var <| eraseVarₚ v) γE))
| _ ▹ _, _  ,       _, .vz   => .vz
| _ ▹ _, γₛE, ⟨γE, _⟩, .vs v => .vs (guardVarₚ γₛE γE v)

/-- Given `"Vec.cons n x v" : "Vec n"`, we change it to `"VecG.cons n x v vG" : "VecG n (VecE.cons n x v)"`.
  Here, note that we construct `"vG" : "VecG n v"`; in general for every inductive argument. -/
def guardTmₚ (γₛE : ConₛA (eraseConₛ Γₛ)) (γE : ConₚA (eraseConₚ Γ) γₛE)
  : (tm : Tmₚ Γ A) ->
    Tmₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA (eraseTmₚ tm) γE))
| Tmₚ.var v => .var (guardVarₚ γₛE γE v)
| Tmₚ.app (A := _A) t u => .app (guardTmₚ γₛE γE t) u
| Tmₚ.appr t u =>
  let e := TmₚA (eraseTmₚ u) γE
  let g := guardTmₚ γₛE γE u
  .appr (.app (guardTmₚ γₛE γE t) e) g

#print axioms guardTmₚ

-- # Example time!

inductive VecE : Type u where
| nil : VecE
| cons : Nat -> String -> VecE -> VecE

inductive VecG : Nat -> VecE -> Type u where
| nil : VecG 0 .nil
| cons : (n : Nat) -> (x:String) -> (e : VecE) -> VecG n e -> VecG (n+1) (VecE.cons n x e)

#reduce guardTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var .vz)
#reduce guardTmₚ (Γₛ := Vₛ) (Γ := V String) ⟨⟨⟩, VecE⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ (.var (.vs .vz))

/-- VecG : Nat -> VecE -> Type -/
example : guardConₛ Vₛ ⟨⟨⟩, VecE⟩ = (⬝ ▹ SPi Nat fun _ => SPi VecE fun _ => U) := rfl
#reduce guardConₚ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (V String) ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩

-- # Lowering

-- ## Sorts

/-- For example maps `"Vec 123"` to `⟨("VecE", "VecG 123"⟩`. -/
def lowerTmₛ {Γₛ : Conₛ} {Aₛ : Tyₛ} (γₛE : ConₛA (eraseConₛ Γₛ))
  (t : Tmₛ Γₛ Aₛ)
  : Tmₛ (eraseConₛ Γₛ) U × Tmₛ (guardConₛ Γₛ γₛE) (guardTyₛ Aₛ (TmₛA (eraseTmₛ t) γₛE))
  := ⟨eraseTmₛ t, guardTmₛ γₛE t⟩

/-- We want to obtain the actual `(e : VecE) × VecG e`. -/
def lowerTmₛA (γₛE : ConₛA.{0, 0} (eraseConₛ Γₛ)) (γₛG : ConₛA (guardConₛ Γₛ γₛE)) (T : Tmₛ Γₛ U) : Type
  := @Sigma (TmₛA (eraseTmₛ T) γₛE) (TmₛA (guardTmₛ γₛE T) γₛG)

/-- `"Vec 123" : "U"` becomes `⟨"VecE", "VecG 123"⟩ : "U" × "VecE -> U"` -/
example : lowerTmₛ (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ (.app (.var .vz) 123)
  = ⟨.var .vz, .app (.var .vz) 123⟩
  := rfl

example : lowerTmₛA (Γₛ := Vₛ) ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ (.app (.var .vz) 123)
  = ((e : VecE) × VecG 123 e)
  := rfl


-- ## Points

/-- Given a term `"Vec.cons n x v"`, produce
  `⟨"VecE.cons n x vᴱ", "VecG.cons n x vᴳ"⟩ : Tmₛ ["VecE"] "U" × Tmₛ ["VecG"] "VecE -> U"`. -/
def lowerTmₚ {Γₛ : Conₛ} {Γ : Conₚ Γₛ} {A : Tyₚ Γₛ} {γₛE} {γE : ConₚA (eraseConₚ Γ) γₛE}
  (t : Tmₚ Γ A)
  : Tmₚ (eraseConₚ Γ) (eraseTyₚ A) × Tmₚ (guardConₚ γₛE Γ γE) (guardTyₚ γₛE A (TmₚA (eraseTmₚ t) γE))
  := ⟨eraseTmₚ t, guardTmₚ γₛE γE t⟩

/-- Given `"Vec.cons ..." : "Vec 123"`, produce `⟨"VecE.cons ...", "VecG.cons ..."⟩ : @Sigma VecE (VecG 123)`.
  Here,  -/
def lowerTmₚA (γₛE : ConₛA (eraseConₛ Γₛ)) (γₛG : ConₛA (guardConₛ Γₛ γₛE))
  (γE : ConₚA (eraseConₚ Γ) γₛE) (γG : ConₚA (guardConₚ γₛE Γ γE) γₛG)
  (t : Tmₚ Γ (El T))
  : lowerTmₛA γₛE γₛG T
  := by
    let g := TmₚA (guardTmₚ γₛE γE t) γG
    rw [guardTyₚ] at g
    rw [TyₚA] at g
    rw [TmₛA] at g
    exact ⟨TmₚA (eraseTmₚ t) γE, g⟩


example : lowerTmₚA (Γₛ := Vₛ) (Γ := V String)
  ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩ ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
  (.var (.vs .vz))
  = ⟨VecE.nil, VecG.nil⟩ := rfl

#check V_cons
/-
def V_cons {A : Type} : Tyₚ Vₛ :=
  PPi Nat fun n =>                     -- (n : Nat) ->
    PPi A fun _ =>                     -- A ->
      PFunc (.app (Tmₛ.var vz) n) <|   -- Vec n ->
        El (.app (Tmₛ.var vz) (n + 1)) -- Vec (n + 1)
-/

-- example : lowerTmₚA (Γₛ := Vₛ) (Γ := V String)
--   ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩
--   ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
--   (.appr (.app (.app (.var .vz) 0) "foo") (.var (.vs .vz)))
--   = ⟨VecE.cons 0 "" VecE.nil, VecG.cons 0 "" VecE.nil VecG.nil⟩
--   := rfl

-- the same as above, just with needless let binders
example : lowerTmₚA (Γₛ := Vₛ) (Γ := V String)
  ⟨⟨⟩, VecE⟩ ⟨⟨⟩, VecG⟩
  ⟨⟨⟨⟩, VecE.nil⟩, VecE.cons⟩ ⟨⟨⟨⟩, VecG.nil⟩, VecG.cons⟩
  (
    let asdf1 : Tmₚ (V String) (PPi String fun _x => PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app (.var .vz) 0
    let asdf2 : Tmₚ (V String) (                     PFunc (.app (Tmₛ.var vz) 0) (El _)) := .app asdf1 "" -- ! if you inline `asdf1` it breaks
    let asdf3 : Tmₚ (V String) (                                                 (El _)) := .appr asdf2 (.var (.vs .vz))
    asdf3 -- ! if you inline asdf3 is breaks as well
  )
  = ⟨VecE.cons 0 "" VecE.nil, VecG.cons 0 "" VecE.nil VecG.nil⟩
  := rfl

/- We first apply `VecE.rec`, then inside each branch we apply `VecG.rec`. -/
def Vec.reconstruct : (e : VecE) -> VecG n e -> Vec String n
| .nil        , g => let .nil := g; .nil
| .cons n x vE, g => let .cons n x vE vG := g; .cons n x (reconstruct vE vG)

/- TODO We need to show that theorems about VecEG are equiv to theorems about Vec.
  So given
-/
#check 1
