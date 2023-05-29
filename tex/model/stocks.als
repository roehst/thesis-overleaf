open util/graph[Security]
open util/ordering[Id]

abstract sig Date {}

sig Stakeholder, Issuer, StockClass {}

sig Id {}

abstract sig Security {
  transactions : disj set Transaction,
  stakeholder : one Stakeholder,
  parent : lone Security
}

fact {
  transactions = ~security
}

abstract sig Transaction {
  id : disj one Id,
  security : one Security
}

sig Issuance extends Transaction {
  stockClass : one StockClass,
  shares : one Int,
  issuedTo : one Stakeholder
}

sig Acceptance extends Transaction {}

sig Cancellation extends Transaction {
  shares : one Int,
  balancingSecurity : lone Security - security
}

sig Transfer extends Transaction {
  shares : one Int,
  to : one Stakeholder,
  resultingSecurity : one Security - security, 
  balancingSecurity : lone Security - security - resultingSecurity
}

// sig SecurityConversion extends Transaction {}
sig Repurchase extends Transaction {
  shares : one Int,
  balancingSecurity : lone Security - security
}

let TerminalTransaction = Cancellation + Transfer + Repurchase + Split + Transfer
let InitialTransaction = Issuance
let NonTerminalTransaction = Acceptance

check {
  TerminalTransaction + InitialTransaction + NonTerminalTransaction = Transaction
}

fact {
  all stock : Security |
    let txs = stock.transactions |
      #(TerminalTransaction & txs) = 1
}

pred pending[sec : Security] { issued[sec] and not accepted[sec] }
pred accepted[sec : Security] { one s : Acceptance | s.security = sec }
pred issued[sec : Security] { one s : Issuance | s.security = sec }
pred cancelled[sec : Security] { one c : Cancellation | c.security = sec }
pred transferred[sec : Security] { one t : Transfer | t.security = sec }
pred splited[sec : Security] { one s : Split | s.security = sec }
pred repurchased[sec : Security] { one r : Repurchase | r.security = sec }

fact { all s : Security | issued[s] }

fact { all sec : Security | accepted[sec] => issued[sec] }
fact { all sec : Security | cancelled[sec] => accepted[sec] }
fact { all sec : Security | transferred[sec] => accepted[sec] }
fact { all sec : Security | splited[sec] => accepted[sec] }
fact { all sec : Security | repurchased[sec] => accepted[sec] }

fact { no sec : Security | transferred[sec] and cancelled[sec] }
fact { no sec : Security | transferred[sec] and splited[sec] }
fact { no sec : Security | transferred[sec] and repurchased[sec] }
fact { no sec : Security | cancelled[sec] and splited[sec] }
fact { no sec : Security | cancelled[sec] and repurchased[sec] }
fact { no sec : Security | splited[sec] and repurchased[sec] }

fact { all c : Cancellation | some c.balancingSecurity => issued[c.balancingSecurity] }
fact { all c : Transfer | some c.balancingSecurity => issued[c.balancingSecurity] }
fact { all c : Repurchase | some c.balancingSecurity => issued[c.balancingSecurity] }

fact { all c : Split | some c.resultingSecurity => issued[c.resultingSecurity] }
fact { all c : Transfer | some c.resultingSecurity => issued[c.resultingSecurity] }

fact {
  all c : Cancellation 
  | one c.balancingSecurity => c.balancingSecurity.parent = c.security
}

fact {
  all t : Transfer
  | one t.resultingSecurity => t.resultingSecurity.parent = t.security
    and one t.balancingSecurity => t.balancingSecurity.parent = t.security
}

fact {
  all r : Repurchase
  | one r.balancingSecurity => r.balancingSecurity.parent = r.security
}

fact {
  all s : Split
  | one s.resultingSecurity => s.resultingSecurity.parent = s.security
}

// Check that the `lone Security - security - resultingSecurity` trick works
check { all s : Transfer | s.security != s.resultingSecurity }


// And finally, to witness the ridiculous power of Alloy
fact {
  tree[parent]
}

sig Split extends Transaction {
  resultingSecurity : one Security
}

// fact {
//   all s : Split 
//     | issued[s.resultingSecurity]
//     and s.resultingSecurity.stakeholder = s.security.stakeholder
//     and s.resultingSecurity.stockClass = s.security.stockClass
//     and s.security != s.resultingSecurity
// }

// A security can not be both a balancing security and a resulting security
fact {
  no s : Security | isBalancingSecurity[s] and isResultingSecurity[s]
}

pred isBalancingSecurity[sec : Security] {
  one t : Transfer | t.balancingSecurity = sec
}

pred isResultingSecurity[sec : Security] {
  one t : Transfer | t.resultingSecurity = sec
}

fact {
  all t : Transfer | some t.balancingSecurity implies t.security = t.balancingSecurity.parent
}

twoSecs : run {
	#Security = 2 and one Repurchase
} for 10
