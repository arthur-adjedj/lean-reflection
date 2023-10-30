import Reflection.Vec
import Reflection.Simple.Recursor
import Reflection.Simple.Constructors
import Reflection.Simple.Iotas

import Reflection.ListN -- for testing

class SimpleInductiveType (T : Type) where
  K : Nat
  ctors : Vec (SCtor T) K
  recursor : Rec ctors
  iotas : (k : Fin K) -> Iota ctors recursor k

namespace Test

instance : SimpleInductiveType Nat := {
  ctors :=
    ⟨.nil      , Nat.zero, SCtorArgs.head Nat.zero⟩ :::
    ⟨.self .nil, Nat.succ, SCtorArgs.recursive fun (n : Nat) => SCtorArgs.head (Nat.succ n)⟩ ::: ⟦⟧
  recursor := @Nat.rec
  iotas := fun
    | 0 => Nat.iota_succ
    | 1 => Nat.iota_zero
}

def ListN.nilArgs : SCtorArgs ListN (.nil) ListN.nil :=
  SCtorArgs.head ListN.nil
def ListN.consArgs : SCtorArgs ListN (.other Nat (.self .nil)) ListN.cons :=
  SCtorArgs.nonrecursive fun (n : Nat) =>
    SCtorArgs.recursive fun (list : ListN) =>
      SCtorArgs.head <| ListN.cons n list

instance : SimpleInductiveType ListN := {
  ctors :=
    ⟨.nil                   , ListN.nil,  ListN.nilArgs⟩ :::
    ⟨.other Nat (.self .nil), ListN.cons, ListN.consArgs⟩ ::: ⟦⟧
  recursor := @ListN.rec
  iotas := fun
    | 0 => ListN.iota_cons
    | 1 => ListN.iota_nil
}

#unify Iota instSimpleInductiveTypeListN.ctors @ListN.rec 0 =?=
  (motive : ListN -> Prop) ->
  (case_nil : motive ListN.nil) ->
  (case_cons : (head : Nat) → (tail : ListN) → motive tail → motive (ListN.cons head tail)) ->
  (head : Nat) ->
  (tail : ListN) ->
  @ListN.rec motive case_nil case_cons (ListN.cons head tail)
      = case_cons head tail (@ListN.rec motive case_nil case_cons tail)

end Test
