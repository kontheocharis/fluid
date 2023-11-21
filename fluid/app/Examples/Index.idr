data Natural : Type where
  Zero : Natural
  Successor : Natural -> Natural

add : Natural -> Natural -> Natural
add Zero n = n
add (Successor m) n = Successor (add m n)
