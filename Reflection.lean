infixr:35 " ×' "  => PProd

inductive ListN : Type where
| nil : ListN
| cons : Nat -> ListN -> ListN

inductive Tree : Type where
| leaf : Tree
| node : Nat -> Tree -> Tree -> Tree

#check Tree.rec
/- {motive : Tree → Sort u} →
  motive Tree.leaf →
  ((a : Nat) → (a_1 a_2 : Tree) → motive a_1 → motive a_2 → motive (Tree.node a a_1 a_2)) →
  (t : Tree) →
  motive t
-/

#check Nat.rec
/- {motive : Nat → Sort u} →
  motive Nat.zero →
  ((n : Nat) → motive n → motive (Nat.succ n)) →
  (t : Nat) →
  motive t
-/

#check ListN.rec
/- {motive : ListN → Sort u} →
  motive ListN.nil →
  ((a : Nat) → (a_1 : ListN) → motive a_1 → motive (ListN.cons a a_1)) →
  (t : ListN) →
  motive t
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

-- abbrev SCtor T := (spec : SCtorSpec) × (ctor : SCtorType T spec) × SCtorArgs T spec ctor
structure SCtor (T : Type) where
  spec : SCtorSpec
  ctor : SCtorType T spec
  args : SCtorArgs T spec ctor

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

def RecCases (motive : T -> Prop) : List (SCtor T) -> Prop
| [] => (t : T) -> motive t
| ⟨spec, ctor, hctor⟩ :: rest => RecCase motive spec ctor hctor id -> RecCases motive rest

/-- Computes the recursor type for the given constructor spec. -/
def Rec : List (SCtor T) -> Prop
| ctors => (motive : T -> Prop) -> RecCases motive ctors

def IotaIntroArgs (motive : T -> Prop)
  (i_spec : SCtorSpec) (i_ctor : SCtorType T i_spec) (i_h : SCtorArgs T i_spec i_ctor)
  -- (ctors : List (SCtor T))
  -- (recursor : @Rec T ctors)
  (i_case : RecCase motive i_spec i_ctor i_h id)
  (fin : (t : T) -> motive t)
  : (spec : SCtorSpec) -> (ctor : SCtorType T spec) -> SCtorArgs T spec ctor -> Prop
| .nil             , ctor, .head .. => fin ctor = i_case sorry
| .self    specTail, ctor, .recursive .. => (a : T) -> sorry
| .other U specTail, ctor, .nonrecursive .. => sorry

def x := 5

def IotaIntroCases₂ (motive : T -> Prop)
  (cont : ((t : T) -> motive t) → Prop)
  : (cs : List (SCtor T)) -> RecCases motive cs -> Prop
| [], (fin : (t : T) -> motive t) => cont fin
| ⟨j_spec, j_ctor, j_hctor⟩ :: rest, fin =>
    (j_case : RecCase motive j_spec j_ctor j_hctor id) ->
      IotaIntroCases₂ motive cont rest (fin j_case)

/-- In `Pre` we collect the cases forall binders. -/
def IotaIntroCases₁
  (motivate : ((motive : T -> Prop) -> Prop) -> Prop)
  : (cs : List (SCtor T)) -> ((motive : T -> Prop) -> RecCases motive cs) -> Type
| [], _fin => Unit
| ⟨j_spec, j_ctor, j_hctor⟩ :: rest, (fin /-: (motive : T -> Prop) -> RecCase motive j_spec j_ctor j_hctor id -> RecCases motive rest-/) =>

  let thisIota : Prop :=
    motivate fun (motive : T -> Prop) =>
      (j_case : RecCase motive j_spec j_ctor j_hctor id) ->
        let cont : ((t : T) -> motive t) → Prop := fun (fin' : (t : T) -> motive t) =>
          IotaIntroArgs motive j_spec j_ctor j_hctor j_case fin' j_spec j_ctor j_hctor
        IotaIntroCases₂ motive cont rest (fin motive j_case)

  let tailIotas : Type := IotaIntroCases₁ motivate rest
    (fun (motive : T -> Prop) (P : Prop -> Prop) => fin motive (fun (j_case : RecCase motive j_spec j_ctor j_hctor id) => P j_case) j_case)

  thisIota ×' tailIotas

def Iotas (ctors : List (SCtor T)) (recursor : @Rec T ctors) : Type
  := IotaIntroCases₁ (fun P => (motive : T -> Prop) -> P motive) (fun _ => id) ctors recursor

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

structure SIType (T : Type) where
  ctors : List (SCtor T)
  recursor : Rec ctors
  -- iotas : Iotas ctors recursor ctors

inductive SType : Type -> Type 1 where
| ind  : SIType A           -> SType A
| func : SType A -> SType B -> SType (A -> B)

def sNat : SIType Nat := {
  ctors := [
    ⟨.nil      , Nat.zero, SCtorArgs.head Nat.zero⟩,
    ⟨.self .nil, Nat.succ, SCtorArgs.recursive fun (n : Nat) => SCtorArgs.head (Nat.succ n)⟩]
  recursor := @Nat.rec
}

def cNil : SCtorArgs ListN (.nil) ListN.nil := SCtorArgs.head ListN.nil
def cCons : SCtorArgs ListN (.other Nat (.self .nil)) ListN.cons :=
  SCtorArgs.nonrecursive <| fun (n : Nat) =>
    SCtorArgs.recursive <| fun (list : ListN) =>
      SCtorArgs.head <| ListN.cons n list

def sListN : SIType ListN := {
  ctors := [
    ⟨.nil                   , ListN.nil,  cNil⟩,
    ⟨.other Nat (.self .nil), ListN.cons, cCons⟩]
  recursor := @ListN.rec
}

def translate' (T : Type) : SIType T -> (E : Type) -> (G : E -> Prop) -> SIType U
| ⟨⟨spec, c, hc⟩ :: cs, recursor⟩ => sorry
| ⟨[], recursor⟩ => sorry

inductive HType : Type -> Type 1
| simple {A : Type} : SIType A -> HType A
| func {A B : Type} : HType A -> HType B -> HType (A -> B)

inductive HVal : (T : Type) -> HType T -> T -> Type

set_option genInjectivity false in
inductive HProp : Prop -> Type 1
| and {α β : Prop} : HProp α -> HProp β -> HProp (And α β)
| app (T : Type) (x : T) (h : HType T) : @HVal T h x -> (P : T -> Prop) -> HProp (P x)
-- gen_injective_theorems% HProp


