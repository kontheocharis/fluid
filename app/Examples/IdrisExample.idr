-- import Data.Nat
-- import Data.Vect


index : (i : Nat) -> (l : List t ) -> Maybe t
index _ [] = Nothing
index Z (x::_) = (Just x)
index (S n) (_::xs) = ((index n) xs)


indexDep : (n : Nat) -> (i : Fin n) -> (l : Vect n t) -> t
indexDep _ _ [] impossible
indexDep _ FZ (x::_) = x
indexDep (S k) (FS f) (_::xs) = (((indexDep k) f ) xs)

drop : (i : Nat) -> (l : List t) -> List t
drop Z xs = xs
drop (S i) [] = []
drop (S i) (_::xs) = ((drop i) xs)


-- drop11 : (n : Nat) -> (i : Nat) -> (l : List t) -> List t
-- drop11 n Z xs = xs
-- drop11 Z (S i) [] = []
-- drop11 (S n) (S i) (_::xs) = (((drop11 n) i) xs)


--assume we have vectToList
vectToList : Vect m a -> List a
vectToList [] = []
vectToList (x::xs) = x::(vectToList xs)

drop12 : (n : Nat) -> (i : Nat) -> (v : Vect n t) -> List t
drop12 n Z xs = (vectToList xs)
drop12 Z (S i) [] = []
drop12 (S n) (S i) (_::xs) = (((drop12 n) i) xs)




drop2 : (n : Nat) -> (i : Nat) -> (v : Vect n t) -> Nat ** Vect k t
drop2 n Z xs = (n ** xs)
drop2 Z (S i) [] = (Z ** [])
drop2 (S n) (S i) (_::xs) = (((drop2 n) i) xs)

drop3 : (n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> Nat ** Vect k t
drop3 n Z LTEZero xs = (n ** xs)
drop3 Z (S i) _ [] impossible
drop3 (S n) (S i) (LTESucc p') (_::xs) = ((((drop3 n) i) p') xs)



drop4 : (n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> (k : Nat) -> (q : k = ((minus n) i)) -> Vect k t
drop4 n Z LTEZero xs _ (Refl _) = ?hole1
        -- rewrite (uu) in xs
        --                                 --previously(n ** xs)
        --                                 --direct return value there
        --                                 --so I need to use rewrite:
        --                                 --need something of type: minus n Z = n
        --     where uu:  (minus n Z = n)
        --         uu =  minusZeroRight  n
        --         uu = ?hole1

drop4 Z (S i) _ [] _ _ impossible
drop4 (S n) (S i) (LTESucc p') (_::xs) _ (S i)) Refl = ((((((drop4 n) i) p') xs) ((minus n) i)) Refl)



drop5 : (n : Nat) -> (i : Nat) -> (p : LTE i n) -> (v : Vect n t) -> Vect ((minus n) i) t
drop5 n Z LTEZero xs = ?hole2
drop5 Z (S i) _ [] impossible
drop5 (S n) (S i) (LTESucc p') (_::xs) = ((((drop5 n) i) p') xs)

-----------------------------------------------------

dropDep : (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m) ->  Vect (minus m n) a
-- dropDep Z m xs p =  rewrite minusZeroRight m in xs
dropDep (S n') (S m') (x :: xs) (LTESucc p')  =   dropDep n' m' xs p'



--TODO:
--remove implicit variable
--pattern match func
--rewrites
