
-- data Equality : (a : Type) -> a -> a -> Type where
--   Reflex : (a : Type) -> (x : a) -> Equality a x x

-- length : (a : Type) -> Array a -> Natural
-- length a (Nil _) = Zero
-- length a (Cons _ _ as) = Successor (length a as)

-- sym : (a : Type) -> (x : a) -> (y : a) -> Equality a x y -> Equality a y x
-- sym a x y (Reflex a x) = Reflex a x

-- cong : (a : Type) -> (b : Type) -> (f : a -> b) -> (x : a) -> (y : a) -> Equality a x y -> Equality b (f x) (f y)
-- cong a b f x y (Reflex a x) = Reflex b (f x)

-- subst : (a : Type) -> (P : a -> Type) -> (x : a) -> (y : a) -> Equality a x y -> P x -> P y
-- subst a P x y (Reflex a x) p = p


data Array : Type -> Type where
  Nil : (a : Type) -> Array a
  Cons : (a : Type) -> a -> Array a -> Array a






-- main : Array Nat
-- main = Cons _ Z (Cons _ (S Z) (Nil _))

data Natural : Type where
  Zero : Natural
  Successor : Natural -> Natural

add : Natural -> Natural -> Natural
add Zero n = n
add (Successor m) n = Successor (add m n)


bain : (a: Type) -> (m: a) -> (Array a) ** (Array a)
bain _ q = (Nil _, Cons _ q (Nil _))


-- main : _
-- main = (\x -> x)

-- ba : Nat
-- ba = main (Z)
