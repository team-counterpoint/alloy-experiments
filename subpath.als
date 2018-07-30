// Team Counterpoint

module subpath[State]

open ctl[State]

sig Path {
	from: disj one State,
	to: disj one State
}

fun pathState: State { Path.from + Path.to }
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

pred path_ag[phi:State] {
	all p:Path | last[p] => p.to not in phi
}

pred path_ax[phi:State] {
	#Path = 1
	Path.to not in phi
}


