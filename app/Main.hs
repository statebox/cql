module Main where

import Language.AQL

emp = "schema S = literal : empty {" ++ "\n" ++
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
	"options"++"\n" ++
		"prover = program"++"\n" ++
    "}"

input = 
	 [--" "
    --  "typeside t = empty \n typeside s = t"
       emp
     ]
{--
attributes
  		first last	: Employee -> string
     	age			: Employee -> nat
     	cummulative_age: Employee -> nat
     	name 		: Department -> string
     observation_equations
     	forall e. cummulative_age(e) = plus(age(e), age(manager(e))) --}

result = map runProg input

main :: IO ()
main = do
  _ <- mapM (putStrLn . show) result
  return ()