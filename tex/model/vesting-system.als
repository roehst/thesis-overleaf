open util/ordering[Date]

/* Vesting triggers will depend on dates and business events */
/* Adding the previous field to Date helps us visualize the sequence of dates */
/* The index field is also helpful for visualization because Alloy's atoms are not ordered */

sig Date {
    previous : lone Date,
    index : one Int
}

abstract sig Event {
}

fact {
    all d : Date {
        d.previous = prev[d]
    }

    all d1, d2 : Date {
        lt[d1, d2] iff lt[d1.index, d2.index]
    }
}

/* The context in which the vesting state is evaluated */
/* is given by the current_date and the current_events */

one sig current_date in Date {}

sig current_events in Event {}

/* A vesting trigger can be triggered (Ok) or not (NotOk) */

abstract sig VestingTrigger {
    status : one Status
}

enum Status {
    Ok, NotOk
}

/* There are two basic VestingTriggers: AfterDate and AfterEvent */

sig AfterDate extends VestingTrigger {
    date : one Date
}

sig AfterEvent extends VestingTrigger {
    event : one Event
}

sig And extends VestingTrigger {
    t1 : one VestingTrigger,
    t2 : one VestingTrigger
}

sig Or extends VestingTrigger {
    t1 : one VestingTrigger,
    t2 : one VestingTrigger
}

sig Not extends VestingTrigger {
    t : one VestingTrigger
}

/* The following facts establish the status of a trigger */
/* under the current context */

fact {
    all ad : AfterDate {
        gte[current_date, ad.date] iff ad.status = Ok
    }
}

fact {
    all ae : AfterEvent {
        ae.event in current_events iff ae.status = Ok
    }
}

fact {
    all a : And {
        (a.t1.status = Ok and a.t2.status = Ok) iff a.status = Ok
    }
}

fact {
    all o : Or {
        (o.t1.status = Ok or o.t2.status = Ok) iff o.status = Ok
    }
}

fact {
    all n : Not {
        (n.t.status = Ok) iff n.status = NotOk
    }
}

/* A vesting condition maps a number of shares to a trigger */
/* The status field is the same as the status of the trigger */

sig VestingCondition {
    shares : one Int,
    trigger : one VestingTrigger,
    status : one Status
} {
    pos[shares]
}

fact {
    all vc : VestingCondition {
        vc.status = Ok iff vc.trigger.status = Ok
    }
}

/* A vesting term contains many conditions modeling a vesting schedule */
sig VestingTerm {
    shares : one Int,
    conditions : set VestingCondition
}

fact {
    all t : VestingTerm {
        eq[t.shares, sum vc : t.conditions | vc.shares]
    }
}

/* Additional constraints to aid in visualization by excluding */
/* meaningless instances */
fact {
    // All triggers in the model belong to some condition
    all t : VestingTrigger {
        some vc : VestingCondition {
            vc.trigger = t
        }
    }
}

fact  {
    // all conditions in the model belong to some term
    all vc : VestingCondition {
        some t : VestingTerm {
            vc in t.conditions
        }
    }
}

fun vestedShares[t : VestingTerm] : Int {
    let vestedConditions = { vc : t.conditions | vc.status = Ok } {
        sum vc : vestedConditions | vc.shares
    }
}

fun pendingShares[t : VestingTerm] : Int {
    let pendingConditions = { vc : t.conditions | vc.status = NotOk } {
        sum vc : pendingConditions | vc.shares
    }
}

run {
    some t : VestingTerm {
        vestedShares[t] = 4 and pendingShares[t] = 3
    }
}