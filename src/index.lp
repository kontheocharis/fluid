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