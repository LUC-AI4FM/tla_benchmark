------------------------------- MODULE NBAC -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Proc,  \* Set of processes
    V      \* Values a process can take: {"YES", "NO"}

VARIABLES 
    values,  \* [Proc -> V]
    votes,   \* [Proc -> V \cup {NIL}]
    fd       \* [Proc -> (SUBSET Proc)]

Init == /\ values \in [Proc -> {"NO"}] 
        /\ votes \in [Proc -> {NIL}] 
        /\ fd \in [Proc -> ({})]

Next ==
  LET ChooseMsgs(votes) ==
      \E m \in Seq(Proc) : \A p \in Proc :
          (m[p] = NIL \/ (\E q \in Proc : m[p] = votes[q]))
  IN
  /\ /\* Message sending and receiving *\
     \E newVotes \in [Proc -> V \cup {NIL}] :
        ChooseMsgs(newVotes)
        /\ /\A p \in Proc :
            (newVotes[p] = NIL \/ (\E q \in Proc : votes[q] = newVotes[p]))
     /\ votes' = newVotes
  /\ /\* Failure detector update *\
     \E newFd \in [Proc -> SUBSET Proc] :
        (\A p \in Proc : fd[p] \subseteq newFd[p])
        /\ votes' = votes
        /\ fd' = newFd
  /\ /\* Local transition based on message and failure detector info *\
     \E newValue \in [Proc -> V] :
        (\A p \in Proc :
           (newValue[p] = values[p]
            \/ (votes'[p] \in {"YES", "NO"} /\ votes'[p] = newValue[p])
            \/ ((~(\E q \in fd'[p]: votes[q] = "NO")) => newValue[p] = "YES")))
        /\ votes' = votes
        /\ fd' = fd
        /\ values' = newValue

Spec == Init /\ [][Next]_<<values, votes, fd>>

\* Type correctness invariants
TypeOK ==
  /\ values \in [Proc -> V]
  /\ votes \in [Proc -> V \cup {NIL}]
  /\ fd \in [Proc -> (SUBSET Proc)]

\* Validity condition: If all processes vote "YES", then they must commit to "YES"
Validity ==
  (\A p \in Proc : votes[p] = "YES") => (\A p \in Proc : values[p] = "YES")

Invariant == TypeOK /\ Validity

 fairnessAssumption ==
   WF_vars_<<values, votes, fd>>[Next]

THEOREM Spec => []Invariant
=============================================================================