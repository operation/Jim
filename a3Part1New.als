// Alloy file for CISC 422, Assignment 3, Part 1
module A3Part1

open util/ordering[Time]   // enforces total order on Time

sig Time {}                // instances denote timestamps

sig File {
   time : Time             // every file has exactly one timestamp
}

// create some instances
runPrep1: run {} for 3 
runPrep2: run {some File} for 3
runPrep3: run {some f1, f2 : File | f1 != f2 && f1.time = f2.time} for 3

// ---------------------------------------------------------------------------
// Q1 ------------------------------------------------------------------------

fun getOldest[] : set File {
   {f1 : File | f1.time = first[]}
}

fun getMostRecent[] : set File {
   {f1 : File | f1.time = last[]}
}

fun getSecondOldest[] : set File {
   {f : File | gt[f.time, getOldest[].time] and no f1 : File | lt[f1.time, f.time] and gt[f1.time, getOldest[].time]}
}

fun getTime[F : set File] : Time {
     {t : F.time | no f1 : F | gt[t,f1.time]}
}

// create some instances to test functions above, e.g., 
runQ1a: run {some getOldest[]} for 3
runQ1b: run {some getMostRecent[]} for 3 
runQ1c: run {some getSecondOldest[]} for 3
runQ1d: run {some File && some getTime[File] } for 3 but exactly 3 File, exactly 3 Time 

// ---------------------------------------------------------------------------
// Q2 ------------------------------------------------------------------------
assert Q2a {
   all f1 : getSecondOldest[], f2 :  getOldest[] | lt[getTime[f2], getTime[f1]]
}
// holds or not?
// hold

assert Q2b {
    all f1 : getMostRecent[], f2 :  getSecondOldest[]| gt[getTime[f1], getTime[f2]]
}	 
// holds or not?
// not hold

// your checks for assertions Q2a and Q2b here
// the check for Q2a
check Q2a for 2
check Q2a for 6
// the check for Q2b
check Q2b for 1
check Q2b for 2
// 2 is the smallest possible scope