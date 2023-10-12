module Vars (var, Sub, sub) where

import Lang

-- | Helper function to create a variable without caring about the unique identifier.
var :: String -> Var
var x = Var x 0

-- | A substitution, represented as a list of variable-term pairs.
newtype Sub = Sub [(Var, Term)]

-- | Apply a substitution to a term.
sub :: Sub -> Term -> Term
sub (Sub []) t = t
sub (Sub ((v, t') : s)) t = sub (Sub s) (subVar v t' t)

-- | Substitute a variable for a term in a term.
subVar :: Var -> Term -> Term -> Term
subVar v t' (PiT v' t1 t2) = PiT v' (subVar v t' t1) (subVar v t' t2)
subVar v t' (Lam v' t) = Lam v' (subVar v t' t)
subVar v t' (App t1 t2) = App (subVar v t' t1) (subVar v t' t2)
subVar v t' (SigmaT v' t1 t2) = SigmaT v' (subVar v t' t1) (subVar v t' t2)
subVar v t' (Pair t1 t2) = Pair (subVar v t' t1) (subVar v t' t2)
subVar _ _ TyT = TyT
subVar v t' (V v') = if v == v' then t' else V v'
subVar _ _ (Global s) = Global s
subVar _ _ (Hole i) = Hole i
subVar _ _ NatT = NatT
subVar v t' (ListT t) = ListT (subVar v t' t)
subVar v t' (MaybeT t) = MaybeT (subVar v t' t)
subVar v t' (VectT t n) = VectT (subVar v t' t) (subVar v t' n)
subVar v t' (FinT t) = FinT (subVar v t' t)
subVar v t' (EqT t1 t2) = EqT (subVar v t' t1) (subVar v t' t2)
subVar _ _ FZ = FZ
subVar v t' (FS t) = FS (subVar v t' t)
subVar _ _ Z = Z
subVar v t' (S t) = S (subVar v t' t)
subVar _ _ LNil = LNil
subVar v t' (LCons t1 t2) = LCons (subVar v t' t1) (subVar v t' t2)
subVar _ _ VNil = VNil
subVar v t' (VCons t1 t2) = VCons (subVar v t' t1) (subVar v t' t2)
subVar v t' (MJust t) = MJust (subVar v t' t)
subVar _ _ MNothing = MNothing
