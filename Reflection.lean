import Reflection.Vec
import Reflection.ForallTelescope

infixr:35 " ×' "  => PProd

/-
  # Ctor Spec
-/

inductive SCtorSpec : Type 1 where
| nil   :                      SCtorSpec
| self  :         SCtorSpec -> SCtorSpec
| other : Type -> SCtorSpec -> SCtorSpec

def SCtorType (T : Type) : SCtorSpec -> Type
| .nil          => T
| .self    tail => T -> SCtorType T tail
| .other U tail => U -> SCtorType T tail

inductive SCtorArgs : (T : Type) -> (spec : SCtorSpec) -> SCtorType T spec -> Type 1
| head         : (f : T)                                 -> SCtorArgs T  .nil               f
| recursive    : ((x : T) -> SCtorArgs T specTail (f x)) -> SCtorArgs T (.self    specTail) f
| nonrecursive : ((x : U) -> SCtorArgs T specTail (f x)) -> SCtorArgs T (.other U specTail) f

structure SCtor (T : Type) where
  spec : SCtorSpec
  ctor : SCtorType T spec
  args : SCtorArgs T spec ctor

def SCtorSpec.len : SCtorSpec -> Nat
| .nil => 0
| .self tail => 1 + tail.len
| .other _ tail => 1 + tail.len

def SCtorSpec.Get (T : Type) : (spec : SCtorSpec) -> (i : Fin spec.len) -> Type
| .nil         , dumb => sorry -- absurd
| .self       _, ⟨0, _⟩ => T
| .self    tail, ⟨.succ n, hn⟩ => tail.Get T ⟨n, sorry⟩
| .other U    _, ⟨0, _⟩ => U
| .other _ tail, ⟨.succ n, hn⟩ => tail.Get T ⟨n, sorry⟩

/-- Helper function. Computes the "match arm" in the recursor type for one constructor.
  For example, for `Nat.succ` returns `(n : Nat) -> motive n → motive (Nat.succ n)`.
  The `mots` is a bit of hack to get all motives towards the right, think of it as an accumulator. -/
def RecCase (motive : T -> Prop) (spec : SCtorSpec) (ctor : SCtorType T spec) (h : SCtorArgs T spec ctor) (mots : Prop -> Prop) : Prop :=
  match spec with
  | .nil => mots <| motive ctor
  | .self specTail =>
    (x : T) ->
      let .recursive h' := h
      RecCase motive specTail (ctor x) (h' x) (fun P => mots (motive x -> P))
  | .other U specTail =>
    (x : U) ->
      let .nonrecursive h' := h
      RecCase motive specTail (ctor x) (h' x) mots

def RecCases (motive : T -> Prop) : Vec (SCtor T) k -> Prop
| ⟦⟧ => (t : T) -> motive t
| ⟨spec, ctor, hctor⟩ ::: rest => RecCase motive spec ctor hctor id -> RecCases motive rest

/-- Computes the recursor type for the given constructor spec. -/
def Rec : Vec (SCtor T) k -> Prop
| ctors => (motive : T -> Prop) -> RecCases motive ctors

section Iotas
-- /-- Iota reduction rule for one specific case. -/
-- def Iota
--   (motive : T -> Prop)
--   (fin : T -> Prop)
--   (ctors : Vec (SCtor T) k)
--   (cases : (i : Fin k) -> RecCase motive (Get ctors i).spec (Get ctors i).ctor (Get ctors i).args id)
--   (i : Fin k)
--   (args : (j : Fin (Get ctors i).spec.len) -> (Get ctors i).spec.Get T j)
--   : Prop :=
--   -- := fin ((Get ctors i).ctor ARGS) = cases i ARGS
--     match (Get ctors i).args with
--     | .head f => sorry
--     | _ => sorry


-- def IotaIntroArgs (motive : T -> Prop)
--   (i_spec : SCtorSpec) (i_ctor : SCtorType T i_spec) (i_h : SCtorArgs T i_spec i_ctor)
--   -- (ctors : List (SCtor T))
--   -- (recursor : @Rec T ctors)
--   (i_case : RecCase motive i_spec i_ctor i_h id)
--   (fin : (t : T) -> motive t)
--   : (spec : SCtorSpec) -> (ctor : SCtorType T spec) -> SCtorArgs T spec ctor -> Prop
-- | .nil             , ctor, .head .. => fin ctor = i_case sorry
-- | .self    specTail, ctor, .recursive .. => (a : T) -> sorry
-- | .other U specTail, ctor, .nonrecursive .. => sorry

-- def x := 5

-- def IotaIntroCases₂ (motive : T -> Prop)
--   (cont : ((t : T) -> motive t) → Prop)
--   : (cs : List (SCtor T)) -> RecCases motive cs -> Prop
-- | [], (fin : (t : T) -> motive t) => cont fin
-- | ⟨j_spec, j_ctor, j_hctor⟩ :: rest, fin =>
--     (j_case : RecCase motive j_spec j_ctor j_hctor id) ->
--       IotaIntroCases₂ motive cont rest (fin j_case)

-- /-- In `Pre` we collect the cases forall binders. -/
-- def IotaIntroCases₁
--   (motivate : ((motive : T -> Prop) -> Prop) -> Prop)
--   : (cs : List (SCtor T)) -> ((motive : T -> Prop) -> RecCases motive cs) -> Type
-- | [], _fin => Unit
-- | ⟨j_spec, j_ctor, j_hctor⟩ :: rest, (fin /-: (motive : T -> Prop) -> RecCase motive j_spec j_ctor j_hctor id -> RecCases motive rest-/) =>

--   let thisIota : Prop :=
--     motivate fun (motive : T -> Prop) =>
--       (j_case : RecCase motive j_spec j_ctor j_hctor id) ->
--         let cont : ((t : T) -> motive t) → Prop := fun (fin' : (t : T) -> motive t) =>
--           IotaIntroArgs motive j_spec j_ctor j_hctor j_case fin' j_spec j_ctor j_hctor
--         IotaIntroCases₂ motive cont rest (fin motive j_case)

--   let tailIotas : Type := IotaIntroCases₁ motivate rest
--     (fun (motive : T -> Prop) (P : Prop -> Prop) => fin motive (fun (j_case : RecCase motive j_spec j_ctor j_hctor id) => P j_case) j_case)

--   thisIota ×' tailIotas

-- def SpecLen : SCtorSpec -> Nat
-- | .nil => 0
-- | .self tail => Nat.succ (SpecLen tail)
-- | .other _ tail => Nat.succ (SpecLen tail)

-- def SpecDoms (T : Type) : (spec : SCtorSpec) -> Vec Type (SpecLen spec)
-- | .nil => .nil
-- | .self tail => T ::: SpecDoms T tail
-- | .other U tail => U ::: SpecDoms T tail

-- def Fun : Vec (Sort u) k -> Sort u -> Sort u
-- | .nil, Ret => Ret
-- | .cons x xs, Ret => (_ : x) -> Fun xs Ret

-- def apply (argTypes : Vec (Sort u) k) (f : Fun argTypes Ret) (args : (i : Fin k) -> Get argTypes i) : Ret
--   := sorry

-- def apply₁
--   (argTypes : Vec (Sort u) k)
--   (motive : T -> Prop)
--   (f : RecCases motive ctors)
--   (args : (i : Fin k) -> Get argTypes i)
--   : RecCases motive ⟦⟧
--   :=
--     match argTypes with
--     | ⟦⟧ => sorry
--     | x ::: xs => sorry

-- def apply₂
--   (argTypes : Vec (Sort u) k)
--   (f : )

-- def Iota (ctors : Vec (SCtor T) k) (recursor : @Rec T k ctors) (idx : Fin k) : Prop :=
--   (motive : T -> Prop) ->
--     let Cases : Vec Prop k := Map ctors (fun ⟨spec, ctor, args⟩ => RecCase motive spec ctor args id)
--     ForallTelescopeP Cases fun cases =>
--       let Args : Vec Type _ := SpecDoms T (Get ctors idx).spec
--       ForallTelescopeP Args fun args =>
--         let fin := apply₁ Cases motive (recursor motive) cases
--         let ctor := Get ctors idx |>.ctor
--         fin (apply Args ctor args) = (apply Args (cases idx) args) /- and now all the recursive cases... oof -/


-- def IotasAux (ctors : Vec (SCtor T) k) (recursor : @Rec T k ctors) (idx : Fin k) : Type := sorry

-- def Iotas (ctors : Vec (SCtor T) k) (recursor : @Rec T k ctors) : Type
--   := IotasAux ctors recursor 
--     sorry
--   -- := IotaIntroCases₁ (fun P => (motive : T -> Prop) -> P motive) (fun _ => id) ctors recursor

end Iotas

structure SimpleInductiveType (T : Type) where
  k : Nat
  ctors : Vec (SCtor T) k
  recursor : Rec ctors
  -- iotas : Iotas ctors

#check Nat

theorem Nat_iota_zero (motive : Nat -> Prop)
  (case_zero : motive Nat.zero)
  (case_succ : (n : Nat) -> motive n → motive (Nat.succ n))
  : @Nat.rec motive case_zero case_succ Nat.zero = case_zero
  := Eq.refl _
theorem Nat_iota_succ (motive : Nat -> Prop)
  (case_zero : motive Nat.zero)
  (case_succ : (n : Nat) -> motive n → motive (Nat.succ n))
  (n : Nat)
  : @Nat.rec motive case_zero case_succ (Nat.succ n)
      = case_succ n (@Nat.rec motive case_zero case_succ n)
  := Eq.refl _

inductive ListN : Type where
| nil : ListN
| cons : Nat -> ListN -> ListN

theorem ListN_iota_nil (motive : ListN -> Prop)
  (case_nil : motive ListN.nil)
  (case_cons : (head : Nat) → (tail : ListN) → motive tail → motive (ListN.cons head tail))
  : @ListN.rec motive case_nil case_cons (ListN.nil) = case_nil
  := Eq.refl _
theorem ListN_iota_cons (motive : ListN -> Prop)
  (case_nil : motive ListN.nil)
  (case_cons : (head : Nat) → (tail : ListN) → motive tail → motive (ListN.cons head tail))
  (head : Nat)
  (tail : ListN)
  : @ListN.rec motive case_nil case_cons (ListN.cons head tail)
      = case_cons head tail (@ListN.rec motive case_nil case_cons tail)
  := Eq.refl _

def sNat : SimpleInductiveType Nat := {
  ctors :=
    ⟨.nil      , Nat.zero, SCtorArgs.head Nat.zero⟩ :::
    ⟨.self .nil, Nat.succ, SCtorArgs.recursive fun (n : Nat) => SCtorArgs.head (Nat.succ n)⟩ ::: ⟦⟧
  recursor := @Nat.rec
}

def cNil : SCtorArgs ListN (.nil) ListN.nil := SCtorArgs.head ListN.nil
def cCons : SCtorArgs ListN (.other Nat (.self .nil)) ListN.cons :=
  SCtorArgs.nonrecursive <| fun (n : Nat) =>
    SCtorArgs.recursive <| fun (list : ListN) =>
      SCtorArgs.head <| ListN.cons n list

def sListN : SimpleInductiveType ListN := {
  ctors :=
    ⟨.nil                   , ListN.nil,  cNil⟩ :::
    ⟨.other Nat (.self .nil), ListN.cons, cCons⟩ ::: ⟦⟧
  recursor := @ListN.rec
}

/-
  # Expressions
-/

inductive SimpleType : Type -> Type 2
| ind  {A   : Type} : SimpleInductiveType A        -> SimpleType A
| func {A B : Type} : SimpleType A -> SimpleType B -> SimpleType (A -> B)

def Args : Type -> Type := sorry
def apply : (ctor : SCtorType T spec) -> Args T -> T := sorry

inductive SimpleValue : (T : Type) -> SimpleType T -> T -> Type 2
| ctor
  (ind : SimpleInductiveType T)
  (i : Fin ind.k)
  (args : Args T)
  : SimpleValue T (.ind ind) (apply (Get ind.ctors i).ctor args)
| lam
  {a : SimpleType A}
  {b : SimpleType B}
  (body : A -> B)
  : SimpleValue (A -> B) (.func a b) (fun (arg : A) => body arg)
-- | app {A B : Type}
--   {a : SimpleType A}
--   {b : SimpleType B}
--   (f : A -> B)
--   (fSimple : SimpleValue (A -> B) (SimpleType.func a b) f)
--   (arg : A)
--   (argSimple : SimpleValue A a arg)
--   : SimpleValue B b (f arg)

inductive InductiveType : (U : List Type) -> (I : List Type) -> (U -> I -> Type) -> Type 1

def eraseIndices (T : Type) : SimpleInductiveType T -> ((Erased : Type) × (Guard : Erased -> Prop) × SimpleInductiveType Erased)
| ⟨.succ k, ⟨spec, c, hc⟩ ::: cs, recursor⟩ => sorry
| ⟨0, ⟦⟧, recursor⟩ => sorry

def translate (φ : Prop) : LeanPred φ -> ((φ' : Prop) × SimplePred φ')
| .inductive => eraseIndices
