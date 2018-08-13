// Team Counterpoint

module subpath[State]

open ctl[State]

// Reified State->State relation.
sig Path {
	from: disj one State,
	to: one State
}

// The first link in the path.
one sig P0 in Path {}

// States that are part of the path.
fun pathState: State { Path.from + Path.to }
// A subset of sigma for the path.
fun pathSigma: State -> State { ~from.to }

private pred first[p:Path] { p.from not in Path.to }
private pred last[p:Path] { p.to not in Path.from }

fact {
	// Successive states in path are connected by transitions
	pathSigma in TS.sigma
	// There is an end of the path.
	one p:Path | last[p]
	// There is a beginning of the path.
	one p:Path | first[p]
	// The beginning of the path is in S0.
	all p:Path | first[p] => p.from in TS.S0
	// There are no loops.
	all p:Path | p.from not in p.from.^pathSigma
}

// Counterexample for AX(phi), i.e. witness for EX(!phi). Finite.
pred path_ax[phi:State] {
	#Path = 1
	Path.to not in phi
}

// Counterexample for AG(phi), i.e. witness for EF(!phi). Finite.
pred path_ag[phi:State] {
	all p:Path | last[p] => p.to not in phi
}

// Counterexample for AF(phi), i.e. witness for EG(!phi). Infite.
pred path_af[phi:State] {
}

// Counterexample for A(phi U si), i.e. witness for E(phi W si). (In)finite.
pred path_au[phi:State] {
}
