// SECTION: Signatures

// SUBSECTION: Stakeholder

sig Stakeholder {
}

// SUBSECTION: Security
sig Security {
  parent : lone Security,
  owner : one Stakeholder
}

// SUBSECTION: Issuance
sig Issuance {
  security : one Security,
  owner : one Stakeholder,
} {
  security.createdBy = this
  no security.parent
  security.owner = owner
}

pred issuanceConditions[i : Issuance] {
	i.security.createdBy = i
	no i.security.parent
}

fact {
	all i : Issuance | issuanceConditions[i]
}

// SUBSECTION: Cancellation
sig Cancellation {
  security : one Security,
  balancingSecurity : lone Security,
}

pred cancellationConditions[c : Cancellation] {
  c.security.destroyedBy = c
  some c.balancingSecurity => c.balancingSecurity.owner = c.security.owner
  some c.balancingSecurity => c.balancingSecurity.parent = c.security
  c.balancingSecurity != c.security
}

fact {
  all c : Cancellation | cancellationConditions[c]
}

// SUBSECTION: Transfer
sig Transfer {
  security : one Security,
  to : one Stakeholder,
  resultingSecurity : one Security,
  balancingSecurity : lone Security
}
pred transferConditions[t : Transfer] {
  t.security.destroyedBy = t
  t.resultingSecurity.createdBy = t
  t.resultingSecurity.owner = t.to
  t.resultingSecurity.parent = t.security
  some t.balancingSecurity => t.balancingSecurity.owner = t.security.owner
  some t.balancingSecurity => t.balancingSecurity.parent = t.security
  t.to != t.security.owner
  t.security != t.resultingSecurity and t.security != t.balancingSecurity and t.resultingSecurity != t.balancingSecurity
}

fact {
  all t : Transfer | transferConditions[t]
}

// SECTION: Constraints

fun trace[sec : Security] : set Security {
  sec.^parent
}

fun portfolio[s : Stakeholder] : set Security {
  { e : Security | e.owner = s }
}

fun createdBy[sec : Security] : one Issuance + Cancellation + Transfer {
  { i : Issuance | i.security = sec }
  + { c : Cancellation | c.balancingSecurity = sec }
  + { t : Transfer | t.balancingSecurity = sec or t.resultingSecurity = sec }
}

fact {
  all s : Security | one s.createdBy
}

fun destroyedBy[sec : Security] : lone Cancellation + Transfer {
  { c : Cancellation | c.security = sec }
  + { t : Transfer | t.security = sec }
}

pred hasCreation[sec : Security] {
  some sec.createdBy
}

pred createdAsBalance[s : Security] {
	s in Cancellation.balancingSecurity
	or s in Transfer.balancingSecurity
}

pred longExample[s : Security] {
	#(s.trace) > 2
}

pred issuanceAlwaysPresent[s : Security] {
	createdBy[s] in Issuance or some v : Security | v in s.trace and createdBy[v] in Issuance
}

// SECTION: Asserts
assert portfoliosAreDisjoint {
  all disj s1, s2 : Stakeholder | portfolio[s1] & portfolio[s2] = none
}

fact noCycles {
  no s : Security | s in s.trace
}

// SECTION: Tests
check portfoliosAreDisjoint for 3
//check noCycles for 3

// SECTION: Examples
example1 : run hasCreation
example2 : run createdAsBalance
example3 : run longExample for 5




