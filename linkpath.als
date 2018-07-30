// Team Counterpoint

module linkpath[State]

open ctl[State]

// Linked list path structure.
sig Path {
	next: lone Path,
	state: disj one State
}

// The first node in the path.
one sig P0 in Path {}

// States that are part of the path.
fun pathState: State { Path.state }
// A subset of sigma for the path.
fun pathSigma: State -> State { ~state.next.state }

private pred finite { some p:Path | no p.next }
private fun last: Path { {p:Path | no p.next} }

fact {
	// Successive states in path are connected by transitions.
	pathSigma in TS.sigma
	// It includes an initial state.
	P0.state in TS.S0
	// The path is connected.
	P0.*next = Path
}

// Counterexample for AX(phi), i.e. witness for EX(!phi). Finite.
pred path_ax[phi:State] {
	#Path = 2
	last.state not in phi
}

// Counterexample for AG(phi), i.e. witness for EF(!phi). Finite.
pred path_ag[phi:State] {
	finite
	last.state not in phi
}

// Counterexample for AF(phi), i.e. witness for EG(!phi). Infite.
pred path_af[phi:State] {
	not finite
	no Path.state & phi
}

// Counterexample for A(phi U si), i.e. witness for E(phi W !si). (In)finite.
pred path_au[phi:State, si:State] {
	finite => last.state in (State - si - phi) else Path.state in phi
}

