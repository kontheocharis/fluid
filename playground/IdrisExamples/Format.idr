
mutual 
    concat : List String -> String 
    concat [] = ""
    concat (s :: ss) = s ++ concat ss 

    showAll : Show a => List a -> String
    showAll = table . map show

    format : List String -> List String
    format []       = []
    format [x]      = [x]
    format (x::xs)   = (x ++ "\n") :: format xs

    table : List String -> String
    table = Main.concat . format

mutual  
    -- Lift format to a type ...
    data Format : (List String) -> Type where 
        C1 : Format [] 
        C2 : (x : String) -> Format [x]
        C3 : (x : String) -> (xs : List String) -> Format xs -> Format ((x ++ "\n") :: xs)

    -- and transform function
 --   showAll2 : Show a => List a -> String
 --   showAll2 = table2 . map show

    format2 : (xs : List String) -> (ind : List String ** Format ind)
    format2 []       = ([] ** C1)
    format2 [x]      = ([x] ** C2 x)
    format2 (x::xs)   = case format2 xs of 
                          (prf ** fmt) => (((x ++ "\n") :: xs) ** C3 x xs ?hole) --  (C3 x xs fmt))

    -- not sure if we need this...
    -- I think there's a (un)fold against Format somewhere here...
    concat' : Format xs -> String 
    concat' C1 = ""
    concat' (C2 x) = x -- might need to put a hole here and ask user to complete.
    concat' (C3 s ss fs) = s ++ concat' fs 
   
    table2 : List String -> String
    table2 xs = case format2 xs of 
                (ind ** fmt) => concat ind
    
            