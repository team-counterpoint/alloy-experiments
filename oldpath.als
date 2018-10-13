// Team Counterpoint

module path[State]

open util/ctl[State]

// ********** Path definition **********

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
private fun loop: Path { {p:Path | p in p.^next} }

fact {
	// Successive states in path are connected by transitions.
	pathSigma in TS.sigma
	// It includes an initial state.
	P0.state in TS.S0
	// The path is connected.
	P0.*next = Path
}

// ********** Non-nested properties **********

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

// Counterexample for AF(phi), i.e. witness for EG(!phi). Infinite.
pred path_af[phi:State] {
	not finite
	no Path.state & phi
}


// Counterexample for A(phi U si), i.e. witness for E(phi W !si). (In)finite.
pred path_au[phi:State, si:State] {
	finite => (Path.state - last.state) in phi and last.state in (State - phi - si)
	else Path.state in phi
}

// Counterexample for A(phi W si), i.e. witness for E(phi U !si). Finite.
pred path_au[phi:State, si:State] {
	finite
	(Path.state - last.state) in phi
	last.state in (State - phi - si)
}

// ********** Specific nested properties **********

// Counterexample for AFAG(phi), i.e. witness for EGEF(!phi). Infinite.
pred path_af_ag[phi:State] {
	not finite
	loop.state not in phi
}

// Counterexample for AGAF(phi), i.e. witness for EFEG(!phi). Infinite.
pred path_ag_af[phi:State] {
	not finite
	no loop.state & phi
}

// Counterexample for AG(phi & AF(si)), i.e. witness for EF(!phi | EG(si)). (In)finite.
pred path_ag_and_af[phi:State, si:State] {
	finite => last.state not in phi else loop.state in si
}

// Counterexample for AF(phi & AF(si)), i.e. witness for EG(!phi | EF(si)). Infinite.
pred path_af_and_ag[phi:State, si:State] {
	not finite
	(no Path.state & phi) or (some loop.state & phi)
}

// Counterexample for AG(phi => AX(si)), i.e. witness for EF(phi & !EX(si)). Finite.
pred path_ag_implies_ax[phi:State, si:State] {
	finite
	last.~next.state in phi
	last.state not in si
}

// Counterexample for AF(phi => AX(si)), i.e. witness for EG(phi & !EX(si)). Infinite.
pred path_ag_implies_ax[phi:State, si:State] {
	not finite
	Path.state in phi
	no Path.next.state & si
}

// ********** Generalized X **********

// issues: internal loops legitimate for EX
// how to decide finiteness
// can make both optional (specify manually)
// -> only issue is with displaying intenral loops  / showing trace
// -> still unambiguous with superstructure
// -> but pathSigma incorrect? state adjacent depends on where you are in path

fun p_ex[phi:State]: State { pathSigma.phi }

fun p_ef[phi:State]: State { (*pathSigma).phi }

fun p_eg[phi:State]: State { {s:pathState | s.*pathSigma in phi} }

fun p_eu[phi:State, si:State]: State {
	*(phi <: pathSigma).(si & (State - phi))
}

pred p_finite[phi: State] { finite and P0.state in phi }
pred p_infinite[phi: State] { not finite and P0.state in phi }


