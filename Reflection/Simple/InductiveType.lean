import Reflection.Vec
import Reflection.Simple.Constructors
import Reflection.Simple.Recursor
-- import Reflection.Simple.Iotas

import Reflection.ListN -- just for testing

class SimpleInductiveType (T : Type) where
  K : Nat
  ctors : Vec (SCtor T) K
  recursor : Rec ctors
  -- iotas : (k : Fin K) -> Iota ctors recursor k

namespace Test

  instance : SimpleInductiveType Nat := {
    ctors :=
      ⟨.nil      , Nat.zero, SCtorArgs.head Nat.zero⟩ :::
      ⟨.self .nil, Nat.succ, SCtorArgs.recursive fun (n : Nat) => SCtorArgs.head (Nat.succ n)⟩ ::: ⟦⟧
    recursor := @Nat.rec
    -- iotas := fun
    --   | 0 => Nat.iota_zero
    --   | 1 => Nat.iota_succ
  }

  def cNil : SCtorArgs ListN (.nil) ListN.nil :=
    SCtorArgs.head ListN.nil
  def cCons : SCtorArgs ListN (.other Nat (.self .nil)) ListN.cons :=
    SCtorArgs.nonrecursive fun (n : Nat) =>
      SCtorArgs.recursive fun (list : ListN) =>
        SCtorArgs.head <| ListN.cons n list

  instance : SimpleInductiveType ListN := {
    ctors :=
      ⟨.nil                   , ListN.nil,  cNil⟩ :::
      ⟨.other Nat (.self .nil), ListN.cons, cCons⟩ ::: ⟦⟧
    recursor := @ListN.rec
  }

end Test
