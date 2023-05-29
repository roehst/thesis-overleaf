// Here we give a simplified model of the OCF security tracing model.
open util/graph[Security]

// SECTION: Signatures

// SUBSECTION: The Security

sig Security {
	shares : one Int,
	parent : lone Security
}

// SUBSECTION: The Abstract Transaction

abstract sig Transaction {}

// SUBSECTION: The Issuance

// All securities are created by an issuance. This gives a nice entry point for modeling how many shares are created, and allows one to establish constraints based on accounting rules.
sig Issuance extends Transaction {
  security : one Security,
  amount : one Int
}

// SUBSECTION: The Cancellation

// Cancellations destroy securities, but a partial cancellation is possible. In this case, a new balancing security is created so that the number of shares balances.
sig Cancellation extends Transaction {
  security : one Security,
  amount : one Int,
  balancingSecurity : lone Security
}

// SUBSECTION: The Transfer

// Transfers always create a resulting security, but if the transfer is partial, a balancing security is created so that the number of shares balances.
sig Transfer extends Transaction {
  security : one Security,
  amount : one Int,
  from : one Stakeholder,
  to : one Stakeholder,
  balancingSecurity : lone Security,
  resultingSecurity : one Security
}

abstract sig Stakeholder {}

// SECTION: Constraints

// SUBSECTION: Requiring that all securities are created by an issuance
fact giveIssuanceToBalancingSecurity {
  all c : Cancellation | some c.balancingSecurity implies one i : Issuance | i.security = c.security
}

fact giveIssuanceToResultingSecurity {
  all t : Transfer | one i : Issuance | i.security = t.resultingSecurity
}

// SUBSECTION: Avoiding cycles
fact noSelfParent {
  no s : Security | s in s.^parent
}

// SUBSECTION: Constraining the parent-child relationship. This is essential for preparing the model to work the tracing.

fact establishParent {
  all t : Transfer | some t.balancingSecurity => t.balancingSecurity.parent = t.security
  all t : Transfer | t.resultingSecurity.parent = t.security
  all i : Issuance | no i.security.parent
  all c : Cancellation | some c.balancingSecurity => c.balancingSecurity.parent = c.security
}

// SUBSECTION: Giving meaningful values to amounts
fact issuancesAlwaysPositive {
  all i : Issuance | pos[i.amount]
  all c : Cancellation | pos[c.amount]
  all t : Transfer | pos[t.amount]
}


// SUBSECTION: Balancing the number of shares

fact cancellationBalances {
  all c : Cancellation 
  | some c.balancingSecurity <=> add[c.balancingSecurity.shares, c.amount] = c.security.shares

  all c : Cancellation 
  | no c.balancingSecurity <=> c.amount = c.security.shares
}

fact issuanceBalances {
  all i : Issuance | i.security.shares = i.amount
}

// SECTION: Funs, or queries
fun history[s : Security] : set Transaction {
  s.*parent
}

// SECTION: Examples

e1 : run {
	some Cancellation
}

e2 : run {
  some Transfer
}

e3 : run {
  some Issuance
}