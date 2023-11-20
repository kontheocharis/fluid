data Finn : Nat -> Type where
  FZZ : Finn (S n)
  FSS : Finn n -> Finn (S n)

index : (t : Type) -> List t -> Nat -> Maybe (List t)
index _ [] _ = Nothing
index _ (x::_) Z = Just x
index t (_::xs) (S n) = index t xs n

