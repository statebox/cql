typeside Type = literal {
	types 
		String
	constants
		gecko frog human cow horse dolphin fish : String
}

schema C = literal : Type {
	entities 
		Amphibian
		LandAnimal
		WaterAnimal
	foreign_keys
		IsAL: Amphibian -> LandAnimal
		IsAW: Amphibian -> WaterAnimal
	attributes
		attA: Amphibian -> String 
		attL: LandAnimal -> String 
		attW: WaterAnimal -> String
	options
		allow_empty_sorts_unsafe = true	
}

instance I = literal : C {
	generators 
		a1 a2 : Amphibian
		l1 l2 l3 l4 l5 : LandAnimal
		w1 w2 w3 w4 : WaterAnimal
	equations
		 attA(a1) = gecko attA(a2) = frog
		 attL(l1) = gecko attL(l2) = frog 
		 attL(l3) = human attL(l4) = cow 
		 attL(l5) = horse attW(w1) = fish 
		 attW(w2) = gecko attW(w3) = frog 
		 attW(w4) = dolphin IsAL(a1) = l1 
		 IsAL(a2) = l2 IsAW(a1) = w2 IsAW(a2) = w3
} 

schema D = literal : Type {
	entities 
		yAmphibian
		yLandAnimal
		yWaterAnimal
		yAnimal
	foreign_keys
		yIsAL:yAmphibian->yLandAnimal
		yIsAW:yAmphibian->yWaterAnimal
		yIsALL:yLandAnimal->yAnimal
		yIsAWW:yWaterAnimal->yAnimal
	path_equations
		yIsAL.yIsALL = yIsAW.yIsAWW
	attributes
		yattA:yAmphibian->String 
		yattL:yLandAnimal->String 
		yattW:yWaterAnimal->String
	options
		allow_empty_sorts_unsafe = true	
		program_allow_nontermination_unsafe = true	
} 

mapping F = literal : C -> D {
	entity
		Amphibian->yAmphibian
	foreign_keys
		IsAL -> yIsAL
		IsAW -> yIsAW
	attributes
		attA -> lambda x. x.yattA

	entity
		LandAnimal->yLandAnimal
	attributes
		attL -> lambda x. x.yattL

	entity
		WaterAnimal->yWaterAnimal
	attributes
		attW -> lambda x. x.yattW
} 

instance J = sigma F I {
	options
		prover = program	
		program_allow_nontermination_unsafe = true
		allow_empty_sorts_unsafe = true	
}

instance I1 = literal : C {
	generators 
		xa1 : Amphibian
		xl1 xl2 xl3 xl4 : LandAnimal
		xw1 xw2 xw3: WaterAnimal
	equations
		attL(xl1) = gecko attL(xl2) = frog
		attL(xl3) = human attL(xl4) = cow
		attW(xw1) = fish attW(xw2) = gecko
		attW(xw3) = frog IsAL(xa1) = xl1
		IsAW(xa1) = xw2 attA(xa1) = gecko
} 

transform t = literal : I1 -> I {
	generators 
		xa1 -> a1
		xl1 -> l1
		xl2 -> l2
		xl3 -> l3
		xl4 -> l4
		xw1 -> w1
		xw2 -> w2
		xw3 -> w3
} 

transform u = sigma F t {
	options
		program_allow_nontermination_unsafe = true
		allow_empty_sorts_unsafe = true
}


instance K = delta F J

transform v = unit F I {
	options
		program_allow_nontermination_unsafe = true
		allow_empty_sorts_unsafe = true
}

