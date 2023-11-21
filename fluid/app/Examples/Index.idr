data Natural : Type where
  Zero : Natural
  Successor : Natural -> Natural

data Array : Type -> Type where
  Nil : (a : Type) -> Array a
  Cons : (a : Type) -> a -> Array a -> Array a

add : Natural -> Natural -> Natural
add Zero n = n
add (Successor m) n = Successor (add m n)

length : (a : Type) -> Array a -> Natural
length a (Nil _) = Zero
length a (Cons _ _ as) = Successor (length a as)
