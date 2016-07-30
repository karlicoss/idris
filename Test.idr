module Test
  
main : IO ()
main = putStrLn "Hello!"

data Vec : Nat -> Type -> Type where
  Nil  : Vec 0 a
  (::) : (x : a) -> (xs : Vec n a) -> Vec (n + 1) a
  


pcrhs_Z : b = plus b 0
pcrhs_Z {b = Z} = Refl
pcrhs_Z {b = (S k)} = let rec = pcrhs_Z {b = k} in
                          rewrite rec in Refl
 
plus_comm_S : S (m + k) = m + (S k)
plus_comm_S {m = Z} {k} = Refl
plus_comm_S {m = S n} {k} = let rec = plus_comm_S {m = n} {k = k} in rewrite rec in Refl 

plus_comm : plus a b = plus b a
plus_comm {a = Z} {b} = pcrhs_Z
plus_comm {a = S k} {b} = let rec = plus_comm {a = k} {b = b} in rewrite rec in plus_comm_S

