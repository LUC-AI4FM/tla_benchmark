------------------------------ MODULE Lock ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS PROC \* set of process identifiers, e.g., {0,1}

VARIABLES
  turn,
  flag,
  h_turn,
  s

(* Helper definition for critical section membership *)
InCS(i) == flag[i] /\ turn = i

Init ==
  /\ turn = 0
  /\ flag = [p \in PROC |-> FALSE]
  /\ h_turn = << >>
  /\ s = 0

(* Action: process p acquires the lock (entry protocol via stuttering variable) *)
Acquire(p) ==
  LET q == CHOOSE x \in PROC : x # p IN
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ turn' = q
    /\ h_turn' = Append(h_turn, turn')
    /\ s' = 2

(* Action: process p releases the lock *)
Release(p) ==
  /\ flag'[p] = FALSE
  /\ s' = 0

(* Stuttering step to model a three-step entry protocol *)
Stutter ==
  /\ s > 0
  /\ s' = s - 1

Next == ∃ p \in PROC : Acquire(p) \/ Release(p) \/ Stutter

Spec == Init /\ [][Next]_<<turn, flag, h_turn, s>>

(* Safety invariant: mutual exclusion *)
MutualExcl ==
  ∀ i, j \in PROC :
    i # j => ~(InCS(i) /\ InCS(j))

(* History invariant: all entries in the history are valid turn values *)
HistoryInv ==
  ∀ k \in 1..Len(h_turn) : h_turn[k] \in PROC

SpecWithInvs == Spec /\ []MutualExcl /\ []HistoryInv

\* Instantiate the Peterson specification with appropriate substitutions
INSTANCE Peterson WITH
  turn = turn,
  flag = flag

=============================================================================