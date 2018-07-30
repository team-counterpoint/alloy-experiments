// Team Counterpoint

module linkpath[State]

open ctl[State]

// Linked list path structure.
sig Path {
	next: lone Path,
	state: one State
}

fun pathState: State {
	{s:State | s in Path.state}
}

pred first[p:Path] { p not in Path.next }
pred last[p:Path] { no p.next }

fact {
	// Successive states in path are connected by transitions.
	all p:Path | p.next.state in TS.sigma[p.state]
	// There is an end of the path.
	one p:Path | last[p]
	// There is a beginning of the path.
	one p:Path | first[p]
	// The beginning of the path is in S0.
	all p:Path | first[p] => p.state in TS.S0
	// There is only one predecessor.
	all p:Path | lone p.~next
	// There are no loops
	all p:Path | p not in p.^next
}

// Counterexample for AX(phi), i.e. witness for EX(!phi). Finite.
pred path_ax[phi:State] {
	#Path = 2
	Path.next.state not in phi
}

// Counterexample for AG(phi), i.e. witness for EF(!phi). Finite.
pred path_ag[phi:State] {
	all p:Path | last[p] => p.state not in phi
}

// Counterexample for AF(phi), i.e. witness for EG(!phi). Infite.
pred path_af[phi:State] {
}

// Counterexample for A(phi U si), i.e. witness for E(phi W si). (In)finite.
pred path_au[phi:State] {
}


