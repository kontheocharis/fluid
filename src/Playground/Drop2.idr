module Drop2 

import Data.Nat
import Data.Fin 
import Data.Vect

import RefacPrelude

vectToList : Vect n a -> List a 
vectToList xs = toList xs


drop3 : (n : Nat) -> (m : Nat) -> Vect m a -> (p : LTE n m)
     -> (k : Nat ** Vect k a)
drop3 Z m xs p = (m ** xs)
drop3 (S n') Z [] p = (Z ** []) -- technically impossible
                                -- but if we don't pattern match...
drop3 (S n') (S m') (x :: xs) (LTESucc p') = drop3 n' m' xs p'
                                -- we need to pass something to the recursive
                                -- call, so we case split
                                -- here, we have only one possibility b/c
                                -- of the arguments, and it becomes obvious what
                                -- to plug in

