// This is the model for the transaction tracing system
// The improvements we make are:
// 
// - All securities must start with an issuance
// - We add a parent relation to the security
// - We constrain the parent relation to be a forest
// - We show a getAncestry function that traces a security back to its root (issuance)
// - No more non-terminal, non-initial transactions: every security has an initial transaction and may be a terminal transaction, making the model more uniform (including the acceptance transaction)

// The builtin Alloy modules are used for imposing the forest structure
// on the graph of securities, although a DAG should probabily suffice.
open util/graph[Security]

// Also, we make the Security ids ordered
open util/ordering[Id]

// We give the security a parent security, which is key
// for improving the tracing system
sig Security {
  parent : lone Security,
  id : one Id
}

// This is very idiomatic alloy to specify
// that each security has an unique id
// and that we can go back from Id to Security isomorphically
sig Id {
	security : disj one Security
}

fact {
	security = ~id
}

// Here is the constraint that the parent relation is a forest
fact {
  forest[parent]
}

// We will have different types of transactions
abstract sig Transaction {
}

sig Issuance extends Transaction {
  issuedSecurity : disj one Security
}

sig Transfer extends Transaction {
  inputSecurity : disj one Security,
  outputSecurity : disj one Security
} {
  inputSecurity != outputSecurity
}

sig Cancellation extends Transaction {
  cancelledSecurity : disj one Security
}

sig Acceptance extends Transaction {
  proposedSecurity : disj one Security,
  acceptedSecurity : disj one Security
} {
  proposedSecurity != acceptedSecurity
}

// A security is created as:
// 
// - As the issued security of an issuance
// - As the output security of a transfer
fun createdBy[security : Security] : set Transaction {
  {issuance : Issuance | issuance.issuedSecurity = security} +
  {transfer : Transfer | transfer.outputSecurity = security} +
  {acceptance : Acceptance | acceptance.acceptedSecurity = security}
}

// And it MUST be created only once.
fact {
  all sec : Security | #createdBy[sec] = 1
}

// A security is destroyed as:
//
// - As the input security of a transfer
// - As the cancelled security of a cancellation
fun destroyedBy[security : Security] : set Transaction {
  {transfer : Transfer | transfer.inputSecurity = security} +
  {cancellation : Cancellation | cancellation.cancelledSecurity = security} +
  {acceptance : Acceptance | acceptance.proposedSecurity = security}
}

pred destroyed[security : Security] {
  some destroyedBy[security]
}

pred created[security : Security] {
  some createdBy[security]
}

// A security can only be destroyed once if it has created
fact {
  all sec : Security | 
    destroyed[sec] => 
      created[sec]
}


// And it can be destroyed at most once.
fact {
  all sec : Security | lone destroyedBy[sec]
}

// We will define the getParent function
fun getParent[security : Security] : set Security {
  {transfer : Transfer | transfer.outputSecurity = security}.inputSecurity +
  {acceptance : Acceptance | acceptance.acceptedSecurity = security}.proposedSecurity
}

// And use it to constraint the parent relation
fact {
  all sec : Security | sec.parent = getParent[sec]
}

// Child ids are always gt than parent ids, this 
// a (partial) ordering on securities, and a complete
// order given a single ancestry line.
fact {
  all sec : Security | 
    some sec.parent => 
      gte[sec.id, sec.parent.id]
}

// Get the ancestry of a security, and a function
// to get the root ancestor of a security - 
// in its clositive transitive form, it is the
// only security with no parent in an ancestry.
fun getAncestry[security : Security] : set Security {
  security.*parent
}

fun getRootAncestor[security : Security] : set Security {
  { other : getAncestry[security] | no other.parent }
}

// Every ancestry line must trace back to an issuance
fact {
  all root : Security | 
    root in getRootAncestor[root] => 
      createdBy[root] in Issuance
}

// A few interesting cases
oneAcceptance : run { some Acceptance }

oneTransfer : run { some Transfer }

twoIssuances : run { #Issuance = 2 }
