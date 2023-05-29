abstract sig Transaction {
  security : Security
}

sig Issuance extends Transaction {
}

sig Security {
  var transactions : seq Transaction
}

fact {
  transactions = ~security
}
