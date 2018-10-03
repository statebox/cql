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
 "}\n"

emp = "schema S = literal : T {" ++ "\n" ++
	"entities"++ "\n" ++
		"Employee"++"\n" ++
		"Department"++"\n" ++
	"foreign_keys"++"\n" ++
		"manager   : Employee -> Employee"++"\n" ++
		"worksIn   : Employee -> Department"++"\n" ++
		"secretary : Department -> Employee"++"\n" ++
	"path_equations" ++"\n" ++
	--"manager.manager = manager" ++ "\n" ++
		--"manager.worksIn = worksIn"++"\n" ++
  --		"secretary.worksIn = Department"++"\n" ++
  	"attributes"++"\n" ++
  	  "first last : Employee -> string"++"\n" ++
     	"age : Employee -> nat"++"\n" ++
     	"cummulative_age: Employee -> nat"++"\n" ++
     	"name : Department -> string"++"\n" ++
    "observation_equations" ++"\n" ++
  --   	"forall e:Employee. cummulative_age(e) = plus(age(e), age(manager(e)))"++"\n" ++
	"options"++"\n" ++
		"prover = program"++"\n" ++
		"program_allow_nonterm_unsafe = true" ++ "\n" ++
		"allow_empty_sorts_unsafe = true" ++ "\n" ++
    "}\n"

inst = "instance I = literal : S {"++"\n" ++
	"generators" ++"\n" ++
		"a : Employee"++"\n" ++
		--"m s : Department"++"\n" ++
	"equations "++"\n" ++
	"a.manager=a a.worksIn.secretary=a " ++ "\n" ++ 
{--		"first(a) = Al"++"\n" ++
		"first(b) = Bob  last(b) = Bo"++"\n" ++
		"first(c) = Carl "++"\n" ++
		"name(m)  = Math name(s) = CS"++"\n" ++
		"age(a) = age(c) "++"\n" ++
		"manager(a) = b manager(b) = b manager(c) = c"++"\n" ++
		"worksIn(a) = m worksIn(b) = m worksIn(c) = s"++"\n" ++
		"secretary(s) = c secretary(m) = b "++"\n" ++ --}
	--	"secretary(worksIn(a)) = manager(a)"++"\n" ++
	--	"worksIn(a) = worksIn(manager(a))"++"\n" ++
	--	"age(a) = succ(zero)" ++"\n" ++
	--	"age(manager(a)) = zero" ++"\n" ++

	--	"age(a) = zero.succ.succ" ++"\n" ++
	--	"age(manager(a)) = zero.succ" ++"\n" ++
        "options" ++"\n" ++
        "program_allow_nonterm_unsafe = true" ++ "\n" ++
        "allow_empty_sorts_unsafe = true" ++ "\n" ++
        "}\n"    

input = 
	 [ arith ++ emp ++ inst 
--       emp
     ]
{--
 --}

result = map runProg input

main :: IO ()
main = do
  _ <- mapM (putStrLn . f) result
  return ()
 where f (Left x) = x
       f (Right (a,b,c)) = show c

