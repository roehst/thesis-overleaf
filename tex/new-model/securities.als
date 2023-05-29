open util/graph[Security]

sig Security {
	shares : one Int,
	parent : lone Security
}

abstract sig Transaction {}

sig Issuance extends Transaction {
	// Should only be issued once
	issuedSecurity : disj one Security,
	shares : disj one Int
} {
	issuedSecurity.shares = shares
	and no issuedSecurity.parent
	and createdWith[issuedSecurity] = this
}

sig Cancellation extends Transaction {
	cancelledSecurity : one Security,
	balancingSecurity : lone Security,
	shares : disj one Int
} {
	lte[shares, cancelledSecurity.shares]
	and pos[shares]
	and (some balancingSecurity => balancingSecurity.parent = cancelledSecurity)
	and (some createdWith[cancelledSecurity])
	and (destroyedWith[cancelledSecurity] = this)
	and (balancingSecurity != cancelledSecurity)
	and (some balancingSecurity <=> lt[shares, cancelledSecurity.shares])
	and (some balancingSecurity <=> balancingSecurity.shares = sub[cancelledSecurity.shares, shares])
}

fun createdWith[s : Security] : one Transaction {
	issuedSecurity.s + balancingSecurity.s
}

fun destroyedWith[s : Security] : one Transaction {
	cancelledSecurity.s
}

fact {
	all s : Security | some createdWith[s]
}

noDoubleIssuance : check {
	no s : Security | #createdWith[s] > 1
}

noDoubleCancel : check {
	no s : Security | #destroyedWith[s] > 1
}

alwaysIssued : check {
	all s : Security | 
		some destroyedWith[s] => one createdWith[s]
}

isForest : check {
	forest[parent]
}

fun history[s : Security] : set Transaction {
	s.*parent
}

run { some  s : Security | #history[s] > 2 }
