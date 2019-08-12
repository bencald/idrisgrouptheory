module Interfaces

import Data.Vect

%default total
%access public export

infixl 7 <>
infixl 8 <.>
infix 0 `trans`

interface Group g where
  (<>)     : g -> g -> g
  assoc    : (a : g) -> (b : g) -> (c : g) -> a <> (b <> c) = (a <> b) <> c
  identity : g
  leftID   : (a : g) -> identity <> a = a
  leftInv  : (a : g) -> (b : g ** b <> a = identity)

interface Group g => GroupAction g a where
  (<.>)          : g -> a -> a
  assocAction    : (g' : g) -> (g'' : g) -> (a' : a) ->
                    g' <.> (g'' <.> a') = (g' <> g'') <.> a'
  identityAction : (a' : a) -> Interfaces.identity <.> a' = a'

interface Group g => Abelian g where
  op_commutes : (a : g) -> (b : g) -> a <> b = b <> a

data Refinement : (g : Type) -> (f : g -> Bool) -> Type where
  In : (e : g) -> {auto prf : f e = True} -> Refinement g f

interface EquivalenceRelation (r : t -> t -> Type) where
  reflexive : {a : t} -> a `r` a
  symmetric : {a : t} -> {b : t} -> a `r` b -> b `r` a
  transitive : {a : t} -> {b : t} -> {c : t} -> a `r` b -> b `r` c -> a `r` c

interface (Group g, EquivalenceRelation r) =>
  Choice g (f : g -> g) (r : g -> g -> Type) where
    choice      : Group g => {a : g} -> a `r` f a
    welldefined : Group g => {a : g} -> {b : g} -> a `r` b -> f (a) = f (b)
    coherence   : Group g => {a : g} -> {a' : g} -> {b : g} -> {b' : g} ->
                  a `r` a' -> b `r` b' -> f (a <> b) = f (a' <> b')

interface Group g => Subgroup g (f : g -> Bool) where
  op_closure  : Group g => (a : g) -> (b : g) ->
                           {auto prfa : f a = True} ->
                           {auto prfb : f b = True} ->
                           f (a <> b) = True
  id_closure  : Group g => f (Interfaces.identity) = True
  inv_closure : Group g => (a : g) -> {auto prf : f a = True} ->
                           (f (fst $ leftInv a) = True)

data Canon : (g : Type) -> (f : g -> g) -> (r : g -> g -> Type) -> Type where
  InCanon : (a : g) -> {auto prf: a = f a} -> Canon g f r

canonizeOnce : (Group g, Choice g f r) => (a : g) -> f a = f (f a)
canonizeOnce {r} a = welldefined {r} (choice {a})

canonizeLastRight : (Group g, Choice g f r) => f (x <> y) = f (x <> (f y))
canonizeLastRight {g} {f} {r} {x} {y}= let
  xrx  = reflexive {t=g} {r} {a=x}
  yrfy = choice {g} {f} {r} {a=y}
  in coherence {g} {f} {r} {a=x} {a'=x} {b=y} {b'=f y} xrx yrfy

canonizeLastLeft : (Group g, Choice g f r) => f (x <> y) = f ((f x) <> y)
canonizeLastLeft {g} {f} {r} {x} {y}= let
  yry = reflexive {r} {a=y}
  xrfx = choice {g} {f} {r} {a=x}
  in coherence {g} {f} {r} {a= x} {a'= f x} {b=y} {b'=y} xrfx yry

eqLemma : Choice g f r => x = y -> x = f x -> y = f y
eqLemma Refl = id

allEqProofsareEquivalent : (prf1 : x = y) -> (prf2 : x = y) -> prf1 = prf2
allEqProofsareEquivalent Refl Refl = Refl

canonRespectsEq : Choice g f r => {prfx : x = f x} -> (eq : x = y) ->
  InCanon {f} {r} x {prf=prfx} = InCanon {f} {r} y {prf=prfy}
canonRespectsEq {prfx} {prfy} Refl = case allEqProofsareEquivalent prfx prfy of
  Refl => Refl

(Group g, Choice g f r) => Group (Canon g f r) where
  (<>) (InCanon x) (InCanon a)
    = InCanon (f (x <> a)) {prf= (canonizeOnce (x<>a) {r})}
  assoc (InCanon x {prf=prfx}) (InCanon y {prf=prfy}) (InCanon z {prf=prfz})
    = let canLeft   = canonizeLastLeft {g} {f} {r} {x=x<>y} {y=z}
          canRight  = sym $ canonizeLastRight {g} {f} {r} {x} {y=y<>z}
          assocCong = cong {f} $ assoc x y z
          equality  = canRight `trans` assocCong `trans` canLeft
      in canonRespectsEq equality
  identity
    = InCanon (f(identity)) {prf = canonizeOnce (identity) {r}}
  leftID (InCanon y {prf})
    = let
      canLeft   = sym $ canonizeLastLeft {g} {f} {r} {x=identity} {y}
      congIDlaw = cong {f} $ leftID y
      equality  = canLeft `trans` congIDlaw `trans` (sym prf)
      in canonRespectsEq equality
  leftInv (InCanon x)
    = let
      (xInv ** xInvPrf) = leftInv x
      canLeft  = sym $ canonizeLastLeft {g} {f} {r} {x=xInv} {y=x}
      congInv  = cong {f} xInvPrf
      equality = canLeft `trans` congInv
      in ( (InCanon (f xInv) {prf= canonizeOnce {g} {f} {r} xInv}) **
            canonRespectsEq equality)

inRespectsEq : Subgroup g f => {prfx : f x = True} ->
                               (eq : x = y) ->
                               In x {prf=prfx} = In y {prf=prfy}
inRespectsEq {prfx} {prfy} Refl = case allEqProofsareEquivalent prfx prfy of
  Refl => Refl

Subgroup g f => Group (Refinement g f) where
  (<>) (In x) (In y) =
    (In (x<>y) {prf=op_closure x y})
  assoc (In x) (In y) (In z) = inRespectsEq $ assoc x y z
  identity       = (In identity {prf=id_closure {f}})
  leftID (In x)  = inRespectsEq $ leftID x
  leftInv (In x) = ((In (fst $ leftInv x) {prf=inv_closure {f} x}) **
    inRespectsEq $ snd $ leftInv x)

interface (Group g, Group h) => Homomorphism g h (f : g -> h) where
  respectsOp : f (x <> y) = f x <> f y
