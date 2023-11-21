data Finn : Nat -> Type where
  FZZ : Finn (S n)
  FSS : Finn n -> Finn (S n)
