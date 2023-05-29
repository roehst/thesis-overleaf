// CHAPTER: Stock Option Plans

// SECTION: Introduction

// SECTION: Signatures

// A stock plan has a number of reserved shares, which are available
// for awarding stock option securities to employees.

sig StockPlan {
	reservedShares : one Int,
	exercises : disj set Exercise,
	securities : disj set Security
}

// A security, in this context, is a stock option that is awarded to
// an employee. It has a vesting term, which is a set of conditions
// that must be met before the security can be exercised.

// For ease of use, we also relate a security to the stock plan that
// it was awarded under.

sig Security {
	vestingTerm : disj one VestingTerm,
	shares : one Int,
	stockPlan : one StockPlan,
}

sig Issuance {
	security : disj one Security,
	shares : one Int,
	vestingTerm : disj one VestingTerm,
	stockPlan : one StockPlan
}

sig Exercise {
	security : one Security,
	resultingSecurity : one Security,
	stockPlan : one StockPlan,
	shares : one Int
} { pos[shares] }

sig Vesting {}

one sig VestingTerm {
	security : one Security,
    vestingConditions : set Status -> one Int
}

fun vestingTermShares[v : VestingTerm] : set Int {
	v.vestingConditions[Status]
}

enum Status { Vested, Pending }

// SECTION: Functions (Queries)
fun vestedShares[v : VestingTerm] : one Int {
	sum[v.vestingConditions[Vested]]
}

fun pendingShares[v : VestingTerm] : one Int {
	sum[v.vestingConditions[Pending]]
}

fun exercisedShares[v : VestingTerm] : one Int {
	let es = { e : Exercise | e.security = v.security } |
	sum[es.shares]
}

// SECTION: Constraints

// SUBSECTION: Positive Shares constraints

// It is useful to constrain all shares to be positive.
fact {
  all s : Security | pos[s.shares]
  all i : Issuance | pos[i.shares]
  all e : Exercise | pos[e.shares]
}

// SUBSECTION: Relational constraints, so that we can navigate objects easily

fact { 
  stockPlan = ~securities 
  }

fact {
	~security = vestingTerm
}

// SUBSECTION: Accounting equations

fact {
	all s : Security |
		gte[s.shares, sum[s.vestingTerm.vestingConditions[Status]]]
}

fact {
	all i : VestingTerm.vestingConditions[Status] | pos[i]
}

fact { 
  all v : VestingTerm | lte[v.exercisedShares, v.vestedShares] 
}


// EXAMPLES
run { one Exercise } for 8

fullyVestedOption : run { one v: VestingTerm | eq[vestedShares[v], vestingTermShares[v]] }

pendingVestedOption : run { one v: VestingTerm | lt[vestedShares[v], vestingTermShares[v]] }
