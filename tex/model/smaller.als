sig Stakeholder {
}

sig Security {
}

sig Issuance {
  issuedSecurity : one Security,
  issuedTo : one Stakeholder
}

sig Acceptance {
  acceptedSecurity : one Security
}

sig Cancellation {
  cancelledSecurity : one Security
}

sig Transfer {
  inputSecurity : one Security,
  outputSecurity : one Security
}

// Predicates about the state of a security
pred issued[sec : Security] {
  one i : Issuance | i.issuedSecurity = sec
}

pred accepted[sec : Security] {
  one a : Acceptance | a.acceptedSecurity = sec
}

pred outputted[sec : Security] {
  one t : Transfer | t.outputSecurity = sec
}

pred inputted[sec : Security] {
  one t : Transfer | t.inputSecurity = sec
}

pred cancelled[sec : Security] {
  one t : Transfer | t.outputSecurity = sec
}

pred terminated[sec : Security] {
  one c : Cancellation | c.cancelledSecurity = sec
  or one t : Transfer | t.inputSecurity = sec
}

pred initialized[sec : Security] {
  one i : Issuance | i.issuedSecurity = sec
  or one t : Transfer | t.outputSecurity = sec
}

fact {
  no s : Security | issued[s] and outputted[s]
}

fact {
  no s : Security | cancelled[s] and inputted[s]
}

fact {
  all s : Security | cancelled[s] implies #({c : Cancellation | c.cancelledSecurity = s}) = 1
}

fact {
  all s : Security | issued[s] implies #({i : Issuance | i.issuedSecurity = s}) = 1
}

fact {
  all sec : Security | terminated[sec] implies initialized[sec]
}
