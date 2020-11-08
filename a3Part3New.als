// Alloy file for CISC 422, Assignment 3, Part 3
module A3Part3

open util/ordering[Time]

sig File {}

sig Time {}

sig State {
    time : File set -> one Time,
    dependsOn : File set -> set File
}
fact StateFacts {
   // 'dependsOn' is acyclic
   all s : State | no f : File | f->f in ^(s.dependsOn)     
   // or, equivalently: all s : State | no f : File | f in f.^(s.dependsOn) 
}

sig Rule {
    target : File,
    prereqs : set File
}
fact RuleFacts {
   all r1, r2 : Rule | r1 != r2 => r1.target != r2.target     // different rules have different targets
   all r : Rule | some r.prereqs     // no rules without prerequisites

}
   
sig Makefile { 
   rules : set Rule,
   targets : set File,
   hasAsPrereq : File set -> set File
}
fact MakefileFacts {
   // the targets of a makefile are all files that have prerequisites 
   all mf : Makefile | mf.targets = (mf.hasAsPrereq).File
   // no extra rules, i.e., every rule belongs to a makefile
   all r : Rule | some mf : Makefile | r in mf.rules
   // define dependencies among file according to rules
   all mf : Makefile | mf.hasAsPrereq = {f:File, f':File | some r : Rule | f = r.target && f' in r.prereqs}
   // no circular dependencies in rules
   all mf : Makefile | no f : File | f->f in ^(mf.hasAsPrereq)
}

fun getTime[s : State] : Time {
   max[File.(s.time)]    // current time of s is largest timestamp used
}   

pred timeLeft[s : State] {
   getTime[s] != last    // is most recent timestamp used?
}

pred freshAccordingToMakefile[f : File, mf : Makefile, s : State] {
   all f' : f.(mf.hasAsPrereq) | gte[f.(s.time), f'.(s.time)]
}

runPrep3: run {} for 3 but exactly 1 Makefile, exactly 1 State

// -----------------------------------------------------------------------------------
// Q5 --------------------------------------------------------------------------------
pred make[mf : Makefile, s : State, s' : State] {
   s'.dependsOn = s.dependsOn &&
   let stale = {f : File | !freshAccordingToMakefile[f, mf, s]} | 
      let staleTargets = stale & (mf.targets) | 
          let haveStaleTargetAsTransPrereq = ^(mf.hasAsPrereq).staleTargets |
              let toUpdate = (staleTargets + haveStaleTargetAsTransPrereq) |
                  all f : File |
                     (f in toUpdate => getTime[s].next = f.(s'.time)) &&  ((not f in toUpdate) => f.(s.time) = f.(s'.time))// replace with your constraints (just 1 or 2 lines)
}

// generate instances to check
runQ51: run {some mf:Makefile, f:File, s:State, s':State-s |
   !freshAccordingToMakefile[f,mf,s] && make[mf, s, s']} for 3
   but exactly 1 Makefile, exactly 2 State
runQ52: run {some mf:Makefile, s:State, s':State-s | make[mf, s, s']} for 3
   but exactly 1 Makefile, exactly 2 State

// -----------------------------------------------------------------------------------
// Q6 --------------------------------------------------------------------------------
assert Q6a {
       all mk :  Makefile, s, s1, s2 : State |
 	   (make[mk, s, s1] && make[mk, s, s2]) => 
		(getTime[s1] = getTime[s2] &&  s1.dependsOn = s2.dependsOn)
}
// holds or not?
// hold

assert Q6b {
       all mk :  Makefile, s, s1 : State |
	! timeLeft[s] => ! make[mk, s, s1]
}
// holds or not?
// not hold

// your checks for Q6a and Q6b here
check Q6a for 6
//true
check Q6b for 1
//false


// -----------------------------------------------------------------------------------
// Q7 -------------------------------------------------------------------------------
pred fresh[f : File, s : State] {
    all mf : Makefile | freshAccordingToMakefile[f, mf, s]
    }
    
pred fresh[s : State] {
   all f : File | fresh[f, s]
}

// your run commands here to test the predicates above here (optional)

assert Q7a {
   all mf :  Makefile, s, s' : State | make[mf, s, s'] && fresh[s']
}
// holds or not?
// not hold
// your check for Q7a here
check Q7a for 1 //F
check Q7a for 2 //F
check Q7a for 6  //F
// -----------------------------------------------------------------------------------
// Q8 --------------------------------------------------------------------------------

pred sound[mf : Makefile, s : State] {
  all f, f' : File | f->f' in ^(s.dependsOn) => (f in mf.targets and f' in f.(mf.hasAsPrereq))
}

// your run commands here to test the predicate above here (optional)

assert Q8a{
   all mf : Makefile, s : State, s' : State | 
	(sound[mf, s] and (s'.dependsOn) in (s.dependsOn))  => sound[mf, s']
}
// holds or not?
// hold
assert Q8b {
    all mf : Makefile, mf' : Makefile, s : State| 
   	(sound[mf, s] and (mf.hasAsPrereq) in (mf'.hasAsPrereq)) <=> sound[mf', s]
}
// holds or not?
// hold
assert Q8c {
}
// holds or not?
// hold
assert Q8d {
   all mf : Makefile, s : State, s1 : State |
	(make[mf, s, s1] && sound[mf, s]) => fresh[s1]
}
// holds or not?
// holds
// your checks for assertions Q8a through Q8d here
check Q8a for 6
//T
check Q8b for 6
//T
check Q8c for 6
//T
check Q8d for 6
//T
// -----------------------------------------------------------------------------------
// Q9 --------------------------------------------------------------------------------

pred optimal[mf : Makefile, s : State] {
   sound[mf, s] and
	 all f, f' : File | f' in f.(mf.hasAsPrereq) => f' in f.^(s.dependsOn)
}

// your run commands here to test the predicate above here (optional)

assert Q9a {
   all mf : Makefile, s : State, s' : State |
   	(fresh[s] and make[mf, s, s'] and sound[mf, s])  => all f : File |  f.(s'.time) = f.(s.time) 
}
// holds or not?
// not hold
assert Q9b {
    all mf : Makefile, s : State, s' : State |
   	(fresh[s] and make[mf, s, s'] and optimal[mf, s]) => all f : File |  f.(s'.time) = f.(s.time) 
}
// holds or not?
// hold
// your checks for assertions Q9a and Q9b here
check Q9a for 6
check Q9b for 6
// ------------------------------------------------------------------------------------
// Q10  --------------------------------------------------------------------------------

pred touch[f : File, s : State, s' : State] {
   timeLeft[s] and s.dependsOn = s'.dependsOn and f.(s'.time) = getTime[s].next and
   (all f' : File | (not f = f') => f.(s'.time) = f'.(s'.time))
}

// your run commands here to test the predicate above here (optional)

assert Q10a {
   all f : File, s : State, s' : State |
   	touch[f, s, s'] => (f.(s'.time) = getTime[s].next &&
		(all f' : File | (not f = f') => f.(s'.time) = f'.(s'.time)))
}
// holds or not?
// hold
assert Q10b {
   all f : File, s : State, s1 : State | touch[f, s, s1] <=> !fresh[s1]
}
// holds or not?
// not hold
assert Q10c {
   // your constraints here
}
// holds or not?

// your checks for assertions Q10a, Q10b, and Q10c here
check Q10a for 6
//T
check Q10b for 6
//NOT TRUE
check Q10c for 6

