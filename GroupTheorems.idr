module Groups

import Interfaces
import Logic

%default total
%access public export




--Definitions for Idempotent and Identity elements of groups, for use in types
Idempotent : Group g => g -> Type
Idempotent a = a <> a = a
--Idempotent a iff a <> a = a.

Identity : Group g => g -> Type
Identity a = a = identity
--Identity a iff a = identity, mostly used to make types look nicer.

--Dummit & Foote Proposition 1, a 5 part proposition.
{-
(1) the identity of G is unique
(2) for each a in G, a inverse is unique
(3) a inverse inverse = a
(4) (a b) inverse = (b inverse) (a inverse)
(5) Generalized associative law
-}

--(1)
idempotentIsIdentity : Group g => {a : g} -> Idempotent a -> Identity a
idempotentIsIdentity {a} axaisa = let (aInv ** invPrf) = leftInv a
  in
    rewrite sym invPrf in rewrite sym axaisa in rewrite assoc aInv a a in
    rewrite invPrf in rewrite leftID a in axaisa
    --rewrite sym invPrf in rewrite sym axaisa in rewrite assoc b a a in
    --rewrite invPrf     in rewrite leftID a   in axaisa

identityIsUnique : Group g => {a : g} -> ((b : g) -> a <> b = b) -> Identity a
identityIsUnique {a} prf = idempotentIsIdentity $ prf a

--(2)
backwardsIsIdempotent : Group g => {a : g} -> Identity (a<>b) -> Idempotent (b<>a)
backwardsIsIdempotent {a} {b} idPrf = rewrite sym $ assoc b a (b<>a) in
  rewrite assoc a b a in rewrite idPrf in rewrite leftID a in Refl

leftInvisRightInv : Group g => {a : g} -> {b : g} -> Identity(a<>b) -> Identity(b<>a)
leftInvisRightInv = idempotentIsIdentity . backwardsIsIdempotent


rightInv : Group g => (a : g) -> (b ** Identity(a<>b))
rightInv a = let (aInv ** linvPrf) = leftInv a in
  (aInv ** leftInvisRightInv linvPrf)
--Function which gives the right inverse of an element, the same as the left.

getInv : Group g => (a : g) -> (b ** Identity (b<>a) `And` Identity (a<>b))
getInv a = let (aInv ** linvPrf)  = leftInv a
               rinvPrf = leftInvisRightInv linvPrf
  in
    (aInv ** Conj linvPrf rinvPrf)

leftIDisRightID : Group g => {a : g} -> a <> Interfaces.identity = a
leftIDisRightID {a} = let (aInv ** linvPrf) = leftInv a
                          rinvPrf = leftInvisRightInv {a=aInv} {b=a} linvPrf
  in
    rewrite sym linvPrf in rewrite assoc a aInv a in
    rewrite rinvPrf     in leftID a

rightID : Group g => (a : g) -> a <> Interfaces.identity = a
rightID a = leftIDisRightID

--(3)
aInvInvisa : Group g => {a : g} -> Identity (b<>a) -> Identity (c<>b) -> a = c
aInvInvisa {a} {b} {c} idba idcb = rewrite sym $ leftID a in rewrite sym idcb in
  rewrite sym $ assoc c b a in rewrite idba in rewrite rightID c in Refl
--Inverse (Inverse a) = a

--(4)
abInvisbInvaInv : Group g => {a : g} -> Identity(d<>b) -> Identity (c<>a) ->
                  Identity((d<>c)<>(a<>b))
abInvisbInvaInv {a} {b} {c} {d} dbid caid =
  rewrite sym $ assoc d c (a<>b) in rewrite assoc c a b in rewrite caid in
  rewrite leftID b in dbid
--Inverse(a<>b) = Inverse(b)<>Inverse(a)

--(5)

--Proposition 2
{-
Left and right cancellation laws
a <> u = b <> u -> a = b
v <> a = v <> b -> a = b
-}

leftMultInv : Group g => {a : g} -> a <> x = b -> Identity(c<>a) -> x = c <> b
leftMultInv {a} {b} {c} {x} eqPrf idPrf =
  rewrite sym eqPrf in rewrite assoc c a x in rewrite idPrf in
  rewrite leftID x  in Refl

rightMultInv : Group g => {a : g} -> x <> a = b -> Identity(a<>c) -> x = b <> c
rightMultInv {a} {b} {c} {x} eqPrf idPrf = rewrite sym eqPrf in
  rewrite sym $ assoc x a c in rewrite idPrf in rewrite rightID x in Refl

rUniqueSolution : Group g => {a : g} -> a <> x = b -> a <> y = b -> x = y
rUniqueSolution {a} {b} {x} {y} axisb ayisb = let
  (aInv ** aInvPrf) = leftInv a
  xIsAInvB = leftMultInv {a=a} {b=b} {c=aInv} {x=x} axisb aInvPrf
  yIsAInvB = leftMultInv {a=a} {b=b} {c=aInv} {x=y} ayisb aInvPrf
  in
    xIsAInvB `trans` (sym yIsAInvB)

lUniqueSolution : Group g => {a : g} -> x <> a = b -> y <> a = b -> x = y
lUniqueSolution {a} {b} {x} {y} xaisb yaisb = let
  (aInv ** aInvPrf) = rightInv a
  xIsBAInv = rightMultInv {a=a} {b=b} {c=aInv} {x=x} xaisb aInvPrf
  yIsBAInv = rightMultInv {a=a} {b=b} {c=aInv} {x=y} yaisb aInvPrf
  in
    xIsBAInv `trans` (sym yIsBAInv)

--Cancellation laws using uniqueness of solutions

lCancel : Group g => {a : g} -> a <> u = b <> u -> a = b
lCancel prf = lUniqueSolution prf (Refl)

rCancel : Group g => {a : g} -> v <> a = v <> b -> a = b
rCancel prf = rUniqueSolution prf (Refl)

cancel : Group g => {a : g} -> (u <> a = u <> b) `Or` (a <> u = b <> u) -> a = b
cancel (ArgL x) = rCancel x
cancel (ArgR x) = lCancel x


{-
SYLOW'S THEOREM:
PLAN SKETCH
Definition:
  Let G be a group and let p be a prime.
    (1) A subgroup of order p^a for some a > 0 is called a p-group.
        Subgroups of G which are p-groups are called p-subgroups.
    (2) If G is a group of order (p^a)*m where p does not divide m,
        then a subgroup of order p^a is called a Sylow p-subgroup of G.
    (3) The set of Sylow p-subgroups will be written as Syl_p(G) and the
        number of Sylow p-subgroups of G will be denoted by n_p(G).

Sylow's Theorem:
  Let G be a group of order (p^a)*m where p is a prime which does not divide m,
    (1) Sylow p-subgroups of G exist i.e. Syl_p(G) =/= empty
    (2) If P is a Sylow p-subgroup of G and Q is any p-subgroup of G, then there
        exists a g in G such that Q < gPg^-1 i.e. Q is contained in some
        conjugate of P.
    (3) The number of Sylow P-Subgroups of G is of the form 1 + kp, i.e.
        n_p == 1 mod p and n_p | m.
-}
