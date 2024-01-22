
data Data1 : Nat -> Type  where
    C1 : (n1: Nat) -> (n2:Nat) -> Data1 n2


g: (n1:Nat) -> (n2:Nat) ->  Data1 n2
g n1 n2  = C1 n1 n2


--unify first two indices of C1
data Data2 : Nat -> Type  where
    C2 : (n1: Nat) -> Data2 n1


gn: (n1:Nat) -> (n2:Nat) ->  Data2 n2
gn n1 n2  = C2 ?n1 


