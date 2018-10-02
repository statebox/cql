module Main where

import Language.AQL

arith = "typeside T = literal {"++ "\n" ++
	"types"++ "\n" ++
		"string" ++ "\n" ++
 		"nat"++ "\n" ++
	"constants"++ "\n" ++
 		"Al Akin Bob Bo Carl Cork Dan Dunn Math CS : string"++ "\n" ++
 		"zero : nat"++ "\n" ++
 	"functions" 		++ "\n" ++
	 	"succ : nat -> nat"++ "\n" ++
	 	"plus : nat, nat -> nat"++ "\n" ++
	"equations"  ++ "\n" ++
	 	"forall x : nat. plus(zero, x) = x"++ "\n" ++
	 	"forall x y : nat. plus(succ(x),y) = succ(plus(x,y))"++ "\n" ++
	"options"++ "\n" ++
		"prover = program"++ "\n" ++
		"program_allow_nonterm_unsafe = true"++ "\n" ++
 "}"

emp = "schema S = literal : T {" ++ "\n" ++
	"entities"++ "\n" ++
		"Employee"++"\n" ++
		"Department"++"\n" ++
	"foreign_keys"++"\n" ++
		"manager   : Employee -> Employee"++"\n" ++
		"worksIn   : Employee -> Department"++"\n" ++
		"secretary : Department -> Employee"++"\n" ++
	"path_equations" ++"\n" ++
		"manager.worksIn = worksIn"++"\n" ++
  		"secretary.worksIn = Department"++"\n" ++
  	"attributes"++"\n" ++
  	  "first last : Employee -> string"++"\n" ++
     	"age : Employee -> nat"++"\n" ++
     	"cummulative_age: Employee -> nat"++"\n" ++
     	"name : Department -> string"++"\n" ++
    "observation_equations" ++"\n" ++
     	"forall e:Employee. cummulative_age(e) = plus(age(e), age(manager(e)))"++"\n" ++
	"options"++"\n" ++
		"prover = program"++"\n" ++
		"program_allow_nonterm_unsafe = true" ++ "\n" ++
		"allow_empty_sorts_unsafe = true" ++ "\n" ++
    "}"

input = 
	 [ arith ++ emp 
--       emp
     ]
{--
 --}

result = map runProg input

main :: IO ()
main = do
  _ <- mapM (putStrLn . show) result
  return ()