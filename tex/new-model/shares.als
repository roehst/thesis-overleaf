// Desafio = como lidar com diluição?

sig VestingTerm { vestingConditions : disj set VestingCondition }

sig VestingCondition { status : one Status, shares : one Int } { pos[shares] }

sig Participation { shares : one Int } { pos[shares] }

enum Status { Vested, Pending, Terminated, Expired }

sig Exercise extends Participation {}

sig Company {
  plans : disj set Plan,
  participations : disj set Participation,
  
}

enum GrantStatus { Active, Inactive }

sig Grant {
  exercises : disj set Exercise,
  vestingTerm : disj one VestingTerm,
  plan : one Plan,
  grantStatus : one GrantStatus
} {
  grantVestedShares[this] <= grantGrantedShares[this]
  and grantExercisedShares[this] <= grantVestedShares[this]
}

sig Plan {
  grants : disj set Grant,
  reservedShares : one Int
}

fact {
  ~grants = plan
}

fun companyExercisedShares[company : Company] : Int {
  sum e : company.plans.grants.exercises | e.shares
}

fun planExercisedShares[plan : Plan] : Int {
  sum e : plan.grants.exercises | e.shares
}

fun grantExercisedShares[grant : Grant] : Int {
  sum e : grant.exercises | e.shares
}

fun companyGrantedShares[company : Company] : Int {
  sum v : company.plans.grants.vestingTerm.vestingConditions | v.shares
}

fun planGrantedShares[plan : Plan] : Int {
  sum v : plan.grants.vestingTerm.vestingConditions | v.shares
}

fun grantGrantedShares[grant : Grant] : Int {
  sum v : grant.vestingTerm.vestingConditions | v.shares
}

fun companyVestedShares[company : Company] : Int {
  sum u : { v : company.plans.grants.vestingTerm.vestingConditions | v.status = Vested } | u.shares
}

fun planVestedShares[plan : Plan] : Int {
  sum u : { v : plan.grants.vestingTerm.vestingConditions | v.status = Vested } | u.shares
}

fun grantVestedShares[grant : Grant] : Int {
  sum u : { v : grant.vestingTerm.vestingConditions | v.status = Vested } | u.shares
}

// Pending, Terminated, Expired
fun companyPendingShares[company : Company] : Int {
  sum u : { v : company.plans.grants.vestingTerm.vestingConditions | v.status = Pending } | u.shares
}

fun planPendingShares[plan : Plan] : Int {
  sum u : { v : plan.grants.vestingTerm.vestingConditions | v.status = Pending } | u.shares
}

fun grantPendingShares[grant : Grant] : Int {
  sum u : { v : grant.vestingTerm.vestingConditions | v.status = Pending } | u.shares
}

fun companyTerminatedShares[company : Company] : Int {
  sum u : { v : company.plans.grants.vestingTerm.vestingConditions | v.status = Terminated } | u.shares
}

fun planTerminatedShares[plan : Plan] : Int {
  sum u : { v : plan.grants.vestingTerm.vestingConditions | v.status = Terminated } | u.shares
}

fun grantTerminatedShares[grant : Grant] : Int {
  sum u : { v : grant.vestingTerm.vestingConditions | v.status = Terminated } | u.shares
}

fun companyExpiredShares[company : Company] : Int {
  sum u : { v : company.plans.grants.vestingTerm.vestingConditions | v.status = Expired } | u.shares
}

fun planExpiredShares[plan : Plan] : Int {
  sum u : { v : plan.grants.vestingTerm.vestingConditions | v.status = Expired } | u.shares
}

fun grantExpiredShares[grant : Grant] : Int {
  sum u : { v : grant.vestingTerm.vestingConditions | v.status = Expired } | u.shares
}

fun companyFullyDilutedShares[company : Company] : Int {
  sub[
    add[companyNonDilutedShares[company], companyReservedShares[company]], 
    companyExercisedShares[company]]
}

fun companyNonDilutedShares[company : Company] : Int {
  add[sum[company.participations.shares], sum[company.plans.grants.exercises.shares]]
}

fun companyReservedShares[company : Company] : Int {
  sum[company.plans.reservedShares]
}

fact {
  all p : Plan | planGrantedShares[p] <= p.reservedShares
}

// All checks pass.

check {
  all c : Company | companyExercisedShares[c] <= companyGrantedShares[c]
}

check {
  all c : Company | companyExercisedShares[c] <= companyVestedShares[c]
}

check {
  all c : Company | companyVestedShares[c] <= companyGrantedShares[c]
}

fact {
  all g : Grant | some p : g.plan.grants | p = g
}

check {
  all c : Company | companyNonDilutedShares[c] <= companyFullyDilutedShares[c]
} for 3 but exactly 1 Company




