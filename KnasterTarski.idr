module KnasterTarski

import Data.SortedSet as S

Rel : Type -> Type
Rel a = a -> a -> Type

data Reflexive: (r: Rel a) -> Type where
  Reflex: ((x: a) -> r x x) -> Reflexive r

data Transitive: (r: Rel a) -> Type where
  Trans: ((x: a) -> (y: a) -> (z: a) -> r x y -> r y z -> r x z) -> Transitive r

data AntiSymmetric: (e: Rel a) -> (r: Rel a) -> Type where
  AntiSym: ((x: a) -> (y: a) -> r x y -> r y x -> e x y) -> AntiSymmetric e r

class Poset a (eq: Rel a) (order: Rel a) where
  orderRefl : Reflexive order
  orderTrans : Transitive order
  orderAntiSym : AntiSymmetric eq order

data NatLeq : Rel Nat where
  ZLeq : NatLeq 0 x
  SLeq : NatLeq x y -> NatLeq (S x) (S y)

natOrderRefl: (x : Nat) -> NatLeq x x
natOrderRefl Z = ZLeq
natOrderRefl (S k) = SLeq (natOrderRefl k)

natOrderTrans: (x: Nat) -> (y:Nat) -> (z:Nat) -> NatLeq x y -> NatLeq y z -> NatLeq x z
natOrderTrans Z y z ZLeq x2 = ZLeq
natOrderTrans (S k) (S j) (S i) (SLeq x) (SLeq y) = SLeq (natOrderTrans k j i x y)

natOrderAntiSym: (x: Nat) -> (y:Nat) -> NatLeq x y -> NatLeq y x -> x = y
natOrderAntiSym Z Z x1 x2 = Refl
natOrderAntiSym (S k) (S j) (SLeq x) (SLeq y) with (natOrderAntiSym k j x y)
  natOrderAntiSym (S k) (S k) (SLeq x) (SLeq y) | Refl = Refl

instance Poset Nat (=) NatLeq where
  orderRefl = Reflex natOrderRefl
  orderTrans = Trans natOrderTrans
  orderAntiSym = AntiSym natOrderAntiSym

data ContProp: k -> SortedSet k -> Type where
  Contains : ((S.contains e s) = True) -> ContProp e s

data SetCont : {k: Type} -> {o: Ord k} -> (Rel (SortedSet k)) where
  AllIn : ((e: k) -> ContProp e s1 -> ContProp e s2) -> SetCont s1 s2

data SetEq: (x: SortedSet k) -> (y: SortedSet k) -> Type where
  Equiv : SetCont x y -> SetCont y x -> SetEq x y

setOrderRefl: (x: SortedSet k) -> SetCont x x
setOrderRefl x = AllIn ref
  where
    ref : (e: k) -> ContProp e x -> ContProp e x
    ref e (Contains prf) = Contains prf

setOrderTrans: (x: SortedSet k) -> (y: SortedSet k) -> (z: SortedSet k) -> SetCont x y -> SetCont y z -> SetCont x z
setOrderTrans x y z (AllIn f) (AllIn g) = AllIn trans
  where
    trans : (e: k) -> ContProp e x -> ContProp e z
    trans e prf = g e (f e prf)

setOrderAntiSym: (x: SortedSet k) -> (y: SortedSet k) -> SetCont x y -> SetCont y x -> SetEq x y
setOrderAntiSym x y x1 x2 = Equiv x1 x2

instance Poset (SortedSet k) SetEq SetCont where
  orderRefl = Reflex setOrderRefl
  orderTrans = Trans setOrderTrans
  orderAntiSym = AntiSym setOrderAntiSym

class (Poset a eq ord) => Lattice a where
  meet : a -> a -> a
  join : a -> a -> a

-- Local Variables:
-- idris-packages: ("rts" "prelude" "jsrts" "idrisdoc" "effects" "contrib" "base")
-- End:
