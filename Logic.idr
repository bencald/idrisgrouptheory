module Logic

%default total
%access public export

infixl 0 `trans`

axiom : t
axiom = believe_me ()

data And : Type -> Type -> Type where
    Conj : p -> q -> p `And` q

data Or : p -> q -> Type where
   ArgL : p -> p `Or` q
   ArgR : q -> p `Or` q

{-
Not is defined in Prelude
Not : Type -> (Type -> Void)
Not t = t -> Void
-}

and_commutes : (x : Bool) -> (y : Bool) -> x && y = y && x
and_commutes False False = Refl
and_commutes False True  = Refl
and_commutes True  False = Refl
and_commutes True  True  = Refl

or_commutes : (x : Bool) -> (y : Bool) -> x || y = y || x
or_commutes False False = Refl
or_commutes False True  = Refl
or_commutes True False  = Refl
or_commutes True True   = Refl

dm_n_and : {orStatement : p `Or` q} -> Not (p `And` q) -> Not p `Or` Not q
dm_n_and {orStatement} n_p_and_q =
  case orStatement of
    ArgL p' => ArgR $ n_p_and_q . Conj p'
    ArgR q' => ArgL $ n_p_and_q . flip Conj q'

dm_n_or : Not (p `Or` q) -> Not p `And` Not q
dm_n_or n_p_or_q = Conj (n_p_or_q . ArgL) (n_p_or_q . ArgR)

nn_lem : {orStatement : a `Or` Not a} -> Not (Not (a `Or` Not a))
nn_lem {orStatement} n_a_or_na = n_a_or_na orStatement

nn_lem' : Not (Not (a `Or` Not a))
nn_lem' n_a_or_na = case dm_n_or n_a_or_na of Conj n_a n_n_a => n_n_a n_a

notEqTruethenFalse : Not (a = True) -> a = False
notEqTruethenFalse {a = False} contr = Refl
notEqTruethenFalse {a = True} contr = absurd $ contr $ Refl
