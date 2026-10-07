------------------------------ MODULE LockWithAux ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Proc,      \* set of process identifiers; assumed to have exactly 2 distinct elements
  NoOwner    \* distinguished value not in Proc representing that the lock is free

ASSUME
  /\ Proc \in SUBSET Nat
  /\ Cardinality(Proc) = 2
  /\ NoOwner \notin Proc

(*
  Helper selecting the other process in a 2-process system.
*)
Other(i) == CHOOSE j \in Proc: j # i

VARIABLES
  owner,     \* in Proc \cup {NoOwner}; which process (if any) owns the lock
  want,      \* subset of Proc; which processes want the lock
  turn,      \* in Proc; auxiliary "turn" to align with Peterson
  h_turn,    \* sequence of Proc; history of assignments to turn
  s          \* [Proc -> 0..2]; stuttering counter to mimic three-step entry

vars == << owner, want, turn, h_turn, s >>

TypeInv ==
  /\ owner \in Proc \cup {NoOwner}
  /\ want \subseteq Proc
  /\ turn \in Proc
  /\ h_turn \in Seq(Proc)
  /\ s \in [Proc -> 0..2]

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(owner = i /\ owner = j)

OwnerImpliesWants ==
  owner \in Proc => owner \in want

Inv == TypeInv /\ MutualExclusion /\ OwnerImpliesWants

Init ==
  /\ TypeInv
  /\ owner = NoOwner
  /\ want = {}
  /\ h_turn = << >>
  /\ s = [i \in Proc |-> 0]
  /\ turn \in Proc

(*
  Abstract intent to acquire and release the lock.
*)
Want(i) ==
  /\ i \in Proc
  /\ i \notin want
  /\ s[i] = 0
  /\ want' = want \cup {i}
  /\ UNCHANGED << owner, turn, h_turn, s >>

Withdraw(i) ==
  /\ i \in Proc
  /\ i \in want
  /\ owner # i
  /\ want' = want \ {i}
  /\ s' = [s EXCEPT ![i] = 0]
  /\ UNCHANGED << owner, turn, h_turn >>

(*
  Three stuttering substeps to mimic Peterson’s entry protocol:
    - Enter1: set flag[i] := TRUE (modeled by want containing i)
    - Enter2: set turn := Other(i), recorded in h_turn
    - Enter:  wait condition (~flag[j] \/ turn = i), then enter critical section
*)
Enter1(i) ==
  /\ i \in Proc
  /\ i \in want
  /\ s[i] = 0
  /\ s' = [s EXCEPT ![i] = 1]
  /\ UNCHANGED << owner, want, turn, h_turn >>

Enter2(i) ==
  /\ i \in Proc
  /\ i \in want
  /\ s[i] = 1
  /\ s' = [s EXCEPT ![i] = 2]
  /\ turn' = Other(i)
  /\ h_turn' = Append(h_turn, Other(i))
  /\ UNCHANGED << owner, want >>

Enter(i) ==
  /\ i \in Proc
  /\ i \in want
  /\ s[i] = 2
  /\ owner = NoOwner
  /\ (~(Other(i) \in want) \/ turn = i)
  /\ owner' = i
  /\ s' = [s EXCEPT ![i] = 0]
  /\ UNCHANGED << want, turn, h_turn >>

Exit(i) ==
  /\ i \in Proc
  /\ owner = i
  /\ owner' = NoOwner
  /\ want' = want \ {i}
  /\ s' = [s EXCEPT ![i] = 0]
  /\ UNCHANGED << turn, h_turn >>

ProcAct(i) ==
  Want(i) \/ Withdraw(i) \/ Enter1(i) \/ Enter2(i) \/ Enter(i) \/ Exit(i)

Next ==
  \E i \in Proc: ProcAct(i)

Fairness ==
  \A i \in Proc: WF_vars(ProcAct(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  A refinement-oriented view to Peterson:
    - Peterson.flag[i] is abstracted by i \in want
    - Peterson.turn is our auxiliary turn
    - Peterson.pc[i] is abstracted from owner/want/s:
        "crit"  if owner = i
        "wait"  if i \in want /\ s[i] = 2
        "setturn" if i \in want /\ s[i] = 1
        "setflag" if i \in want /\ s[i] = 0
        "idle" otherwise
*)
FlagMap == [i \in Proc |-> i \in want]

PcMap ==
  [ i \in Proc |->
      IF owner = i THEN "crit"
      ELSE IF i \in want THEN
        IF s[i] = 2 THEN "wait"
        ELSE IF s[i] = 1 THEN "setturn"
        ELSE "setflag"
      ELSE "idle"
  ]

Pet == INSTANCE PetersonSpec
        WITH
          Proc <- Proc,
          flag <- FlagMap,
          turn <- turn,
          pc   <- PcMap

===============================================================================