// Alloy file for CISC 422, Assignment 3, Part 2
module A3Part2

open util/ordering[Time]   // enforces total order on Time

sig Time {}

sig File {}

sig State {
   time: File set -> one Time  // in every state, every file has exactly one timestamp
}   

runPrep1: run {some State} for 3 

// ---------------------------------------------------------------------------
// Q3

pred setToSmallerTimestamp[s, s' : State] {
    all f : File | lt[f.(s'.time),f.(s.time)]
}

pred setToNextTimestamp[s, s' : State] {
    all f1 : File | prevs[f1.(s.time)] = f1.(s'.time)
}

// your run commands here to test the predicates above here (optional)
runQ31: run {some s, s': State | setToSmallerTimestamp[s, s']} for 3 but exactly 2 State
runQ32: run {some s, s': State | setToNextTimestamp[s, s']} for 3 but exactly 2 State
// ---------------------------------------------------------------------------
// Q4

fun getMostRecent[s : State] : set File {
   {f: File | no f1:File | gt[f1.(s.time), f.(s.time)]  }
}

assert Q4b1 {
   all s, s' : State |  setToSmallerTimestamp[s, s'] && getMostRecent[s] = getMostRecent[s']
}
// holds or not?
// not hold

assert Q4b2 {
   all s, s' : State |  setToNextTimestamp[s, s'] => getMostRecent[s] = getMostRecent[s']
}
// holds or not?
// hold

pred noTimeLeft[s : State] {
   some (s.time).last 
// or, equivalently, max[File.(s.time)] = last
}

// if there's no time left in s, setToSmallerTimestamp[s, s'] fails
assert ifNoTimeLeftSetToSmallerTimestampFails {
   all s : State | noTimeLeft[s] => all s' : State | !setToSmallerTimestamp[s, s']
}
// holds or not?
// not hold
// if there's no time left in s, setToNextTimestamp[s, s'] fails 
assert ifNoTimeLeftSetToNextTimestampFails {
   all s : State | noTimeLeft[s] => all s' : State | !setToNextTimestamp[s, s']
}
// holds or not?
//hold

// your checks for assertions Q4b1, Q4b2, ifNoTimeLeftSetToSmallerTimestampFails, and ifNoTimeLeftSetToNextTimestampFails here
// the check for assertion Q4b1
check Q4b1 for 1 
check Q4b1 for 2

// the check for assertion Q4b2
check Q4b2 for 1
check Q4b2 for 2
check Q4b2 for 6
// the check for assertion ifNoTimeLeftSetToSmallerTimestampFails
check ifNoTimeLeftSetToSmallerTimestampFails for 2
// the check for assertion ifNoTimeLeftSetToNextTimestampFails
check ifNoTimeLeftSetToNextTimestampFails for 1
check ifNoTimeLeftSetToNextTimestampFails for 2
check ifNoTimeLeftSetToNextTimestampFails for 3
check ifNoTimeLeftSetToNextTimestampFails for 6

