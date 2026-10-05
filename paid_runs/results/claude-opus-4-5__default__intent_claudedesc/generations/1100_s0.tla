------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS TLAPS

CONSTANTS Proc1, Proc2

VARIABLES lock, pc1, pc2

(* Process locations: "ncs" = non-critical section, "wait" = waiting to acquire,
   "cs" = critical section, "exit" = releasing lock *)

TypeOK ==
    /\ lock \in {"free", "held"}
    /\ pc1 \in {"ncs", "wait", "cs", "exit"}
    /\ pc2 \in {"ncs", "wait", "cs", "exit"}

Init ==
    /\ lock = "free"
    /\ pc1 = "ncs"
    /\ pc2 = "ncs"

(* Process 1 actions *)
Enter1 ==
    /\ pc1 = "ncs"
    /\ pc1' = "wait"
    /\ UNCHANGED <<lock, pc2>>

Acquire1 ==
    /\ pc1 = "wait"
    /\ lock = "free"
    /\ lock' = "held"
    /\ pc1' = "cs"
    /\ UNCHANGED pc2

Exit1 ==
    /\ pc1 = "cs"
    /\ pc1' = "exit"
    /\ UNCHANGED <<lock, pc2>>

Release1 ==
    /\ pc1 = "exit"
    /\ lock' = "free"
    /\ pc1' = "ncs"
    /\ UNCHANGED pc2

(* Process 2 actions *)
Enter2 ==
    /\ pc2 = "ncs"
    /\ pc2' = "wait"
    /\ UNCHANGED <<lock, pc1>>

Acquire2 ==
    /\ pc2 = "wait"
    /\ lock = "free"
    /\ lock' = "held"
    /\ pc2' = "cs"
    /\ UNCHANGED pc1

Exit2 ==
    /\ pc2 = "cs"
    /\ pc2' = "exit"
    /\ UNCHANGED <<lock, pc1>>

Release2 ==
    /\ pc2 = "exit"
    /\ lock' = "free"
    /\ pc2' = "ncs"
    /\ UNCHANGED pc1

Next ==
    \/ Enter1 \/ Acquire1 \/ Exit1 \/ Release1
    \/ Enter2 \/ Acquire2 \/ Exit2 \/ Release2

Spec == Init /\ [][Next]_<<lock, pc1, pc2>>

(* Mutual exclusion: no two processes in cs or exit simultaneously,
   and lock reflects when a process holds it *)
MutualExclusion ==
    /\ ~(pc1 \in {"cs", "exit"} /\ pc2 \in {"cs", "exit"})
    /\ (pc1 \in {"cs", "exit"} => lock = "held")
    /\ (pc2 \in {"cs", "exit"} => lock = "held")

(* Combined invariant for induction *)
Inv == TypeOK /\ MutualExclusion

(* ----- TLAPS Proofs ----- *)

THEOREM TypeCorrectness == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_<<lock, pc1, pc2>> => TypeOK'
  <2>1. ASSUME TypeOK, Next
        PROVE TypeOK'
    BY <2>1 DEF TypeOK, Next, Enter1, Acquire1, Exit1, Release1,
                            Enter2, Acquire2, Exit2, Release2
  <2>2. ASSUME TypeOK, UNCHANGED <<lock, pc1, pc2>>
        PROVE TypeOK'
    BY <2>2 DEF TypeOK
  <2>. QED BY <2>1, <2>2
<1>. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusionTheorem == Spec => []MutualExclusion
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, MutualExclusion
<1>2. Inv /\ [Next]_<<lock, pc1, pc2>> => Inv'
  <2>1. ASSUME Inv, Enter1
        PROVE Inv'
    BY <2>1 DEF Inv, TypeOK, MutualExclusion, Enter1
  <2>2. ASSUME Inv, Acquire1
        PROVE Inv'
    BY <2>2 DEF Inv, TypeOK, MutualExclusion, Acquire1
  <2>3. ASSUME Inv, Exit1
        PROVE Inv'
    BY <2>3 DEF Inv, TypeOK, MutualExclusion, Exit1
  <2>4. ASSUME Inv, Release1
        PROVE Inv'
    BY <2>4 DEF Inv, TypeOK, MutualExclusion, Release1
  <2>5. ASSUME Inv, Enter2
        PROVE Inv'
    BY <2>5 DEF Inv, TypeOK, MutualExclusion, Enter2
  <2>6. ASSUME Inv, Acquire2
        PROVE Inv'
    BY <2>6 DEF Inv, TypeOK, MutualExclusion, Acquire2
  <2>7. ASSUME Inv, Exit2
        PROVE Inv'
    BY <2>7 DEF Inv, TypeOK, MutualExclusion, Exit2
  <2>8. ASSUME Inv, Release2
        PROVE Inv'
    BY <2>8 DEF Inv, TypeOK, MutualExclusion, Release2
  <2>9. ASSUME Inv, UNCHANGED <<lock, pc1, pc2>>
        PROVE Inv'
    BY <2>9 DEF Inv, TypeOK, MutualExclusion
  <2>. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9
          DEF Next
<1>3. Inv => MutualExclusion
  BY DEF Inv, MutualExclusion
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================