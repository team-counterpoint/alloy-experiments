open util/ordering[State]

abstract sig Object { eats: set Object }
one sig Farmer, Fox, Chicken, Grain extends Object {}

fact { eats = Fox->Chicken + Chicken->Grain }

sig State { near, far: set Object }

fact { first.near = Object && no first.far }

pred crossRiver[from, from', to, to': set Object] {
	one x: from {
		from' = from - x - Farmer - from'.eats
		to' = to + x + Farmer
	}
}

fact {
	all s: State, s': s.next {
		Farmer in s.near =>
			crossRiver[s.near, s'.near, s.far, s'.far]
		else
			crossRiver[s.far, s'.far, s.near, s'.near]
	}
}

run { last.far = Object } for exactly 8 State
