open util/graph[Security]

// Notas para continuar
// Terminar de restringir a ordem de transações
// de sequencias de transações possíveis;
// Implementar o predicado parent direito, pois
// vai gerar o grafo de securities e isso será fantástico.
// Deixar conversão para defesa.
// Implementar plan security.
// Para cada predicado, mostrar o resultado.
// Constrains aritméticos são necessários?

//
//
// 
// 
//       MODEL SPECIFICATION
// 
// 
//
//

// Some preliminary definitions and signatures

// Giving a date a signature is useful because then we can define relations between dates. open util/ordering[Date]

abstract sig Date {}

// A valuable insight in the OCF is that contracts can speak about numbers in varied ways; we can speak of 25% of shares, of 1/3rd of shares, or of 1000 shares. Originally, the vesting term contains a field for quantities and other for fractions and percentages. We mix both approaches as a more abstract Portion signature.

abstract sig Portion {}

sig Fraction extends Portion {
  numerator : one Int,
  denominator : one Int
}

sig Percentage extends Portion {
  percentage : one Int
}

sig Quantity extends Portion {
  quantity : one Int
}

// See note on enums as abstract signatures. But basically modeling stakeholders as a single signature prevents the model from expressing the fact that a stakeholder might be a company that itself issues shares, and companies can cross-hold investments, in which case calculating taxes and percentage ownership becomes very complicated.
sig Stakeholder {}

// Issuers are those who can issue securities. If stakeholders are companies, then issuers are stakeholders as well. May be this might be another contribution to the model.
sig Issuer {}

// Stock from issuers must always belong to some stock class. Different stock classes carry different obligations and rights. Here, we can add a securities field.
sig StockClass {}

// The signature declared by `sig Security` has no fields, so the only way to compare two instances is via their identity. The signature fulfills the purpose of correlating different transactions. This correlation is the basis for auditability of the system. 
// The transactions field is amazing because it
// helps find the transations for each
// security and avoids any pre conditions
// that in order to add a transaction
// to a security, it must be the same security
// id as other tarnsactions in that security. 
abstract sig Security {
  transactions : disj set Transaction,
  stakeholder : one Stakeholder,
	parent : lone Security
}

fact {
  transactions = ~security
}

sig PlanSecurity, StockSecurity extends Security {}

// Securities undergo transactions, some of which are terminal and some of which are not. There are varied transaction types (given below), and what they have in common is that they "touch" securities, and that they are sequenced. The business logic will be reflected in the sequencing of transactions - not all sequences are valid, and that property can be expressed in Alloy. As we shall see, a security exists only between a initial and a terminal transaction. This hints at finding a category for the transactions, since there are non-initial and non-terminal transactions, that are sequenced, and thus composed.

abstract sig Transaction {
  security : one Security
}

// Since initial transactions always produce shares, terminal transactions always consume shares, and non-terminal transactions both produce and consume shares, every transaction could be given a generalized model in terms of inputs and outputs. This is a contribution to the model. Still, some transactions will have specific fields in their signatures such as a plan security issuance, that must have a vesting term.
// A stock issuance says that a security is issued by an issuer to a stakeholder in a given stock class. An StockSecurityIssuance is an initial transaction. A stock issuance is a initial transaction for a stock security. It assigns a stock class, a quantity of shares and a stakeholder to the security.
sig StockSecurityIssuance extends Transaction {
  stockClass : one StockClass,
  shares : one Quantity,
  issuedTo : one Stakeholder
}

sig StockSecurityAcceptance extends Transaction {}

// A stock cancellation is a terminal transaction, since when the cancellation is total, then the security is consumed, and when the cancellation is partial, then a balancing security is issued.
sig StockSecurityCancellation extends Transaction {
  shares : one Quantity,
  balancingSecurity : lone Security - security
}

// A stock security transfer is a terminal transaction as well, since a partial transfer consumes the security, again possibly issuing a balancing security. An invariant condition of the stock security tranfer is that the security, resulting security and balancing security are disjoint. Here we use a facility of Alloy to express that fact without writing more facts.
sig StockSecurityTransfer extends Transaction {
  shares : one Quantity,
  to : one Stakeholder,
  resultingSecurity : one Security - security, 
  balancingSecurity : lone Security - security - resultingSecurity
}

// sig StockSecurityConversion extends Transaction {}
sig StockSecurityRepurchase extends Transaction {
  shares : one Quantity,
  balancingSecurity : lone Security - security
}

let TerminalTransaction = StockSecurityCancellation + StockSecurityTransfer + StockSecurityRepurchase + StockSecuritySplit + StockSecurityTransfer

fact {
  all stock : StockSecurity |
    let txs = stock.transactions |
      #(TerminalTransaction & txs) = 1
}

pred pending[sec : StockSecurity] { issued[sec] and not accepted[sec] }
pred accepted[sec : StockSecurity] { one s : StockSecurityAcceptance | s.security = sec }
pred issued[sec : StockSecurity] { one s : StockSecurityIssuance | s.security = sec }
pred cancelled[sec : StockSecurity] { one c : StockSecurityCancellation | c.security = sec }
pred transferred[sec : StockSecurity] { one t : StockSecurityTransfer | t.security = sec }
pred splited[sec : StockSecurity] { one s : StockSecuritySplit | s.security = sec }
pred repurchased[sec : StockSecurity] { one r : StockSecurityRepurchase | r.security = sec }

fact { all s : Security | issued[s] }

fact { all sec : StockSecurity | accepted[sec] => issued[sec] }
fact { all sec : StockSecurity | cancelled[sec] => accepted[sec] }
fact { all sec : StockSecurity | transferred[sec] => accepted[sec] }
fact { all sec : StockSecurity | splited[sec] => accepted[sec] }
fact { all sec : StockSecurity | repurchased[sec] => accepted[sec] }

fact { no sec : StockSecurity | transferred[sec] and cancelled[sec] }
fact { no sec : StockSecurity | transferred[sec] and splited[sec] }
fact { no sec : StockSecurity | transferred[sec] and repurchased[sec] }
fact { no sec : StockSecurity | cancelled[sec] and splited[sec] }
fact { no sec : StockSecurity | cancelled[sec] and repurchased[sec] }
fact { no sec : StockSecurity | splited[sec] and repurchased[sec] }

fact { all c : StockSecurityCancellation | some c.balancingSecurity => issued[c.balancingSecurity] }
fact { all c : StockSecurityTransfer | some c.balancingSecurity => issued[c.balancingSecurity] }
fact { all c : StockSecurityRepurchase | some c.balancingSecurity => issued[c.balancingSecurity] }

fact { all c : StockSecuritySplit | some c.resultingSecurity => issued[c.resultingSecurity] }
fact { all c : StockSecurityTransfer | some c.resultingSecurity => issued[c.resultingSecurity] }

fact linkParentsCancellation {
  all c : StockSecurityCancellation 
  | one c.balancingSecurity => c.balancingSecurity.parent = c.security
}

fact linkParentsTransfer {
  all t : StockSecurityTransfer
  | one t.resultingSecurity => t.resultingSecurity.parent = t.security
    and one t.balancingSecurity => t.balancingSecurity.parent = t.security
}

fact linkParentsRepurchase {
  all r : StockSecurityRepurchase
  | one r.balancingSecurity => r.balancingSecurity.parent = r.security
}

fact linkParentsSplit {
  all s : StockSecuritySplit
  | one s.resultingSecurity => s.resultingSecurity.parent = s.security
}

// Check that the `lone Security - security - resultingSecurity` trick works
check { all s : StockSecurityTransfer | s.security != s.resultingSecurity }


// And finally, to witness the ridiculous power of Alloy
fact {
  tree[parent]
}

// Executing "Check check$1"
//    Solver=minisatprover(jni) Bitwidth=4 MaxSeq=4 SkolemDepth=4 Symmetry=20 Mode=batch
//    8168 vars. 876 primary vars. 15993 clauses. 187ms.
//    No counterexample found. . may be valid. 19ms.
//    . reduced from 3 to 2 top-level formulas. 85ms.

// Executing "Check check$2"
//    Solver=minisatprover(jni) Bitwidth=4 MaxSeq=4 SkolemDepth=4 Symmetry=20 Mode=batch
//    8148 vars. 876 primary vars. 15922 clauses. 169ms.
//    No counterexample found. . may be valid. 21ms.
//    . contains 2 top-level formulas. 79ms.

run { one StockSecuritySplit } for 5

rwb : run { 
  one a : StockSecurityCancellation | some a.balancingSecurity
} for 7

// Our stock security split is more powerful than original;
// must be paired with issuance.
sig StockSecuritySplit extends Transaction {
  resultingSecurity : one StockSecurity
}

fact {
  all s : StockSecuritySplit 
    | issued[s.resultingSecurity]
    and s.resultingSecurity.stakeholder = s.security.stakeholder
    and s.resultingSecurity.stockClass = s.security.stockClass
    and s.security != s.resultingSecurity
}

// <PlanSecurityTransactions>

sig PlanSecurityIssuance extends Transaction {
  vestingTerm : one VestingTerm,
  owner : one Stakeholder,
  stockClass : one StockClass
}

sig PlanSecurityAcceptance extends Transaction {
}

sig PlanSecurityCancellation extends Transaction {
  shares : one Int,
  balancingSecurity : one Security
}

sig PlanSecurityExercise extends Transaction {
  shares : one Int,
  resultingSecurity : one Security
}

sig PlanSecurityRelease extends Transaction {
  shares : one Int,
  resultingSecurity : one Security
}

sig PlanSecurityRetraction extends Transaction {
}

sig PlanSecurityTransfer extends Transaction {
  shares : one Int,
  from : one Stakeholder,
  to : one Stakeholder,
  resultingSecurity : one Security
}

// Here we stick to generaility, where in the OCF there are different vesting events for different types of vesting. Here we only mention the condition that was satisfied, which also stipulates the shares. It points to the condition, which points to the vesting term.
sig PlanSecurityVesting extends Transaction {
  condition : one VestingCondition,
  event : lone Event
}

// </PlanSecurityTransactions>
fact {
  all p : PlanSecurityVesting 
    | p.condition in p.condition.vestingTerm.conditions
}

fact {
// PlanSecurityExercise.security in PlanSecurity would work, but // the following is even better because constrains // the security to be a plan security.
  PlanSecurityExercise.security in PlanSecurityIssuance.security
}


let StockSecurityTransaction = 
  StockSecurityIssuance + StockSecurityCancellation + 
  StockSecurityTransfer + StockSecurityAcceptance 
//  + StockSecurityConversion 
  + StockSecurityRepurchase 
//  + StockSecurityRetraction 
//  + StockSecurityReissuance
  + StockSecuritySplit

let PlanSecurityTransaction = 
  PlanSecurityIssuance + PlanSecurityAcceptance + 
  PlanSecurityCancellation + PlanSecurityExercise + 
  PlanSecurityRelease + PlanSecurityRetraction + 
  PlanSecurityTransfer + PlanSecurityVesting

fact {
  StockSecurityTransaction.security in StockSecurity
  PlanSecurityTransaction.security in PlanSecurity
}

// No counter example is found.
// This assures that we don't mix
// plan securities and stock securities.
assert noMixing {
  no StockSecurityTransaction.security & PlanSecurityTransaction.security
}

check noMixing for 5

// Before we define the model for stock option transactions, we must first introduce the key concept of vesting. Vesting means that the right to exercise a stock option is given only according to a given schedule. A common schedule is to vest 1/4th after one year, and then 1/48th every month until the end of the fourth year. This example helps us introduce the concept of a cliff, which is a period of time (in our case, 1 year) during which no vesting occurs - the first year is vested in full at then end of the year, and then the remaining 3 years are vested monthly. This shifts risk from the firm to the employee, since the employee loses his right to exercise the option if he leaves the firm before the end of the cliff.
// We have original contributions here as well, since we see the VestingTerm/VestingCondition/VestingTrigger signatures as a DSL for expressing vesting schedules and rules in general. We can not avoid to ask if the DSL could be extended, and it can. A vesting condition originally has a set of vesting triggers that must conjunctively be satisfied. By introducing And and Or triggers, we can express disjunctive and conjunctive conditions in general. We also add the Not for negation.

sig VestingTerm {
  conditions : disj set VestingCondition,
  shares : one Int // useful for checks
}

// A vesting condition has a portion and one trigger Originally, it had a set of triggers, which needed to be conjunctively satisfied. Since we introduce Or and And operators into the implied vesting schedule DSL, we can have a single trigger per condition.

sig VestingCondition {
  portion : one Portion,
  trigger : one VestingTrigger,
  vestingTerm : one VestingTerm
}

fact {
  vestingTerm = ~conditions
}

abstract sig VestingTrigger {}

//
//
// While the OCF's JSON Schema has triggers for absolute date, relative date and event,
// with properties that stand for labels to differentiate the type
// of trigger and then derive the expected properties,
// 
// We can be more abstract in alloy.
// 
// We improve the original vesting trigger language
// by making it more composable and organizing it more like the
// AST for a language.
// 
//
//

// This triggers when a vesting is schedule on an absolute date.
sig AbsoluteDate extends VestingTrigger {
  date : one Date
}

// Triggers when the vesting period starts, and can be used to model the cliff of a vesting term.
sig VestingStart extends VestingTrigger {}

// And this models vestings scheduled on a relative date, for which the VestingStart is a useful base date.
sig RelativeDate extends VestingTrigger {
  date : one Date
}

// Triggers when the a given event occurs.
sig VestingEvent extends VestingTrigger {
  event : Event
}

// Events are commonly company-events that reward
// employees with accelerated vesting.
// Every condition can have a set of events that
// accerate it.
enum Event {
  CompanyAcquired, 
  CompanyGonePublic, 
  CompanyFinancialMilestoneAchieved
}

// And for much greater expressivity,
// we add the following operators,
// that can be composed with exact dates, for instance.
sig After, Before extends VestingTrigger {
  trigger : one VestingTrigger
}

// Plus boolean operators:
sig And, Or extends VestingTrigger {
  left : one VestingTrigger,
  right : one VestingTrigger
}

sig Not extends VestingTrigger {
  trigger : one VestingTrigger
}

// This greatly improves the expressivity of the vesting schedule DSL. // We can now have vestings that can only be exercised in a given interval, // for example, or between two events occur. // We can plot this with latex as an AST. // And now we can define the stock option transactions. // In order to issue options against a stock, // a plan security issuance is required.

// It is important to have that for all vesting terms vt, the sum of all shares in all vesting conditions is equal to the shares in the vesting term.

pred noOverVesting[v : VestingTerm] {
  int (sum c : v.conditions | c.portion.quantity) < int v.shares
}

fact {
	all v : VestingTerm | noOverVesting[v]
}


//
//


//
//
// MODEL TESTING
//
//

disjointSecuritiesInStockSecurityTransfer : check {
  no s : StockSecurityTransfer | s.security = s.resultingSecurity
  and no s : StockSecurityTransfer | s.security = s.balancingSecurity
  and no s : StockSecurityTransfer | s.resultingSecurity = s.balancingSecurity
}

//
//
// MODEL TESTING - HERE WE TEST THAT TRANSACTIONS DO NOT MIX OVER SECURITIES
//
//

// This is an important function, because
// it gets all transactions of a given security.
fun getStockSecurityTransactions[sec : StockSecurity] : Transaction {
  { tx : StockSecurityIssuance | tx.security = sec }
  + { tx : StockSecurityCancellation | tx.security = sec }
  + { tx : StockSecurityTransfer | tx.security = sec }
  + { tx : StockSecurityTransfer | tx.resultingSecurity = sec }
  + { tx : StockSecurityTransfer | tx.balancingSecurity = sec }
}

fun getPlanSecurityTransactions[sec : PlanSecurity] : Transaction {
  { tx : PlanSecurityIssuance | tx.security = sec }
  + { tx : PlanSecurityExercise | tx.security = sec }
  + { tx : PlanSecurityVesting | tx.security = sec }
  + { tx : PlanSecurityCancellation | tx.security = sec }
}

let PlanTransaction = PlanSecurityIssuance + PlanSecurityExercise + PlanSecurityVesting
	 + PlanSecurityCancellation
let StockTransaction = 
	StockSecurityIssuance + StockSecurityCancellation + StockSecurityTransfer



// Executing "Check checkNoMixedTrasactions"
//    Solver=minisatprover(jni) Bitwidth=4 MaxSeq=4 SkolemDepth=4 Symmetry=20 Mode=batch
//    5765 vars. 795 primary vars. 9525 clauses. 92ms.
//    No counterexample found. . may be valid. 11ms.
//    . reduced from 5 to 4 top-level formulas. 54ms.


// Executing "Check disjointSecuritiesInStockSecurityTransfer"
//    Solver=minisatprover(jni) Bitwidth=4 MaxSeq=4 SkolemDepth=4 Symmetry=20 Mode=batch
//    5724 vars. 798 primary vars. 9504 clauses. 115ms.
//    No counterexample found. . may be valid. 10ms.
//    . reduced from 3 to 2 top-level formulas. 51ms.


run { one PlanSecurityVesting }

// Introducing the concepts of initial, terminal and non-terminal transactions will be useful - because we might define properties that are valid for all transactions in each of the three types.
// A security should have always a single initial transaction, some non-terminal transactions, and possibly a terminal transaction. Securities are thus traces of execution - in the sense that they are transitions of a state (in the sense of state machines). This has the name "Security Tracing" in the OCF.


// It would look a bit like the following, where // we give inputs a type of Security -> Int, // meaning how much of each security is being spent. // Outputs include transfer outputs // and balancing securities. // Another way to look at it is that balancing and resulting securities // are just securities - they have the same signature.
// sig GeneralizedStockSecurityTransfer extends TerminalTransaction {
//   inputs : Security -> Int,
//   outputs : Security,
//   from : one Stakeholder,
//   to : one Stakeholder
// }

twoSecs : run {
	#Security = 2
} for 7