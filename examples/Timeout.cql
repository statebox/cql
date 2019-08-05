
schema S = literal : empty {
       entities E
       foreign_keys f : E -> E
}

instance I = literal : S {
	 generators e : E
	 options timeout = "1"
}
