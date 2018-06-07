sig S {}
sig T {}

one sig Relation {
	R : S some-> T
}

// S ->lone T
pred partial_function[R: S -> T] {
	all s: S | lone s.R
}

// S ->some T
pred total[R: S -> T] {
	all s: S | some s.R
}

// S lone-> T
pred injective[R: S -> T] {
	all t: T | lone R.t
}

// S some-> T
pred surjective[R: S -> T] {
	all t: T | some R.t
}

// Change the multiplicities on R above and then check
// the corresponding predicate.
// check { partial_function[Relation.R] } for 5
