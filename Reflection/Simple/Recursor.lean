import Reflection.Vec
import Reflection.Simple.Constructors

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
| ⟨spec, ctor, hctor⟩ ::: rest => (RecCase motive spec ctor hctor id) -> RecCases motive rest

/-- Computes the recursor type for the given constructor spec. -/
def Rec : Vec (SCtor T) k -> Prop
| ctors => (motive : T -> Prop) -> RecCases motive ctors
