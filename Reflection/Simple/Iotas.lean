import Reflection.Vec
import Reflection.Simple.Constructors
import Reflection.Simple.Recursor

def IotaCasesFairing
  (ctors : Vec (SCtor T) K)
  (recursor : Rec ctors)
  (motive : T -> Prop)
  (k : Fin K)
  (body :
    (base : (t : T) -> motive t) -> -- or maybe this? `RecCases motive ctors ->`
    (case : RecCase motive (Get ctors k).spec (Get ctors k).ctor (Get ctors k).args id) ->
    Prop
  )
  : Prop
  := sorry

-- def IotaArgsFairing
--   (ctors : Vec (SCtor T) K)
--   (recursor : Rec ctors)
--   (motive : T -> Prop)
--   (k : Fin K)
--   -- (taker : SCtorType T (Get ctors k).spec)
--   (body : T -> Prop)
--   : Prop
--   := sorry

def IotaAux 
  (ctors : Vec (SCtor T) K)
  (recursor : Rec ctors)
  (motive : T -> Prop)
  -- (k : Fin K)
  (base : (t : T) -> motive t) -- or maybe this? `RecCases motive ctors ->`
  -- (case : RecCase motive (Get ctors k).spec (Get ctors k).ctor (Get ctors k).args id)
  -- (spec : SCtorSpec)
  -- (ctor : SCtorType T spec)
  :
  (spec : SCtorSpec) ->
  (ctor : SCtorType T spec) -> -- this is also our `t : T`, so the value we are eliminating (note that `SCtorType T []` ==β=> `T`).
  (args : SCtorArgs T spec ctor) ->
  (mots : Prop -> Prop) ->
  (rhs : RecCase motive spec ctor args mots) ->
  Prop
| .nil          , ctor, args, mots, rhs => base ctor = rhs
| .self    spec', ctor, args, mots, rhs =>
  (arg : T) ->
    IotaAux ctors recursor motive base spec' (ctor arg) sorry sorry (base arg)
| .other U spec', ctor, args, mots, rhs =>
  (arg : U) ->
    IotaAux ctors recursor motive base spec' (ctor arg) sorry sorry rhs

def Iota (ctors : Vec (SCtor T) K) (recursor : Rec ctors) (k : Fin K) : Prop :=
  (motive : T -> Prop) ->
    IotaCasesFairing ctors recursor motive k fun base case =>
      IotaAux ctors recursor motive base case (Get ctors k).spec (Get ctors k).ctor
      -- IotaArgsFairing ctors recursor motive k fun t =>
      --   base t = sorry






namespace Test
  structure _SimpleInductiveType (T : Type) where
    K : Nat -- the amount of constructors
    ctors : Vec (SCtor T) K
    recursor : Rec ctors
    iotas : (k : Fin K) -> Iota ctors recursor k
end Test
