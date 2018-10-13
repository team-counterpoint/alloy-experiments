// Team Counterpoint

module path[S]

open ctl[S]

// Linked list path structure.
sig Path {
	next: lone Path,
	state: one S
}

// The first node in the path.
one sig P0 in Path {}

// States that are part of the path.
fun pathState: S { Path.state }
// A subset of sigma for the path.
fun pathSigma: S -> S { ~state.next.state }

private pred finite { some p: Path | no p.next }
private fun last: Path { {p: Path | no p.next} }

fact {
	// Successive states in path are connected by transitions.
	pathSigma in TS.sigma
	// It includes an initial state.
	P0.state in TS.S0
	// The path is connected.
	P0.*next = Path
}

// ********** Generalized X **********

// issues: internal loops legitimate for EX
// how to decide finiteness
// can make both optional (specify manually)
// -> only issue is with displaying intenral loops  / showing trace
// -> still unambiguous with superstructure
// -> but pathSigma incorrect? state adjacent depends on where you are in path

fun p_ex[phi: S]: S { pathSigma.phi }

fun p_ef[phi: S]: S { (*pathSigma).phi }

fun p_eg[phi: S]: S { {s:pathState | s.*pathSigma in phi and (s in s.*pathSigma or ) } }

fun p_eu[phi: S, si: S]: S {
	// why S-phi ??? Should just be .si ?
	*(phi <: pathSigma).(si & (S - phi))
}

fun p_af[phi: S]: S { not_[p_eg[not_[phi]]] }

fun p_ag[phi: S]: S { not_[p_ef[not_[phi]]] }

pred p_ctl_mc[phi: S] { finite }

// assert AFp
// c/e: EG(!p)
// must be infinite...

// NOT [infinite & EG (!p)]
// check: finite | AF p
// check: infinite => AF p

// Problem with just using properties:
// If I say p_af[p], it will give a counterexample
// (aka witness to p_eg[p]) that just stops arbitrarily.
// Forcing user to specify liveness properties
// (e.g. check_liveness[p] doing "infinite => p", so that
//  c/e is infinite & !p) is not sufficient, because what
// if the state space has no infinite paths (it is a tree)?
// There are only dead ends. You can still have AF properties hold!

// Two issues remain:
// 1. EG and dead ends thing
// 2. paths that repeat states (but using pathSigma in definitions...)
// solve these, then finiteness shoudln't be a problem?
// remember to remove "disj"

pred p_finite[phi: S] { finite and P0.state in phi }
pred p_infinite[phi: S] { not finite and P0.state in phi }


