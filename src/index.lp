let index0 =
    ( \a i xs ->
           listElim a
                    (\l -> forall (i :: Nat) . Maybe a)
                    (\i -> Nothing a)
                    (\x xs rec i -> 
                        natElim (\i -> Maybe a)
                                (Just a x)
                                (\i' recN -> rec i') i
                    ) xs i 

    ) :: forall (a :: *) (i :: Nat) (xs :: List a) . Maybe a



let index1 =
    ( \a i n xs ->
           vecElim a
                    (\n l -> forall (i :: Nat) . Maybe a)
                    (\i -> Nothing a)
                    (\n' x xs rec i -> 
                        natElim (\i -> Maybe a)
                                (Just a x)
                                (\i' recN -> rec i') i
                    ) n xs i 

    ) :: forall (a :: *) (i :: Nat) (n :: Nat) (xs :: Vec a n) . Maybe a