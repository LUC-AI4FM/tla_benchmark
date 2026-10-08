MODULE FastMutualExclusion
EXTENDS Naturals, TLC

CONSTANT N \in Nat

VARIABLES x, y, b, ctrl

(* --------------------------------------------------------------------------- *)
(* Type invariant *)
TypeInvariant ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [1..N -> BOOLEAN]
    /\ ctrl \in [1..N -> {"Idle","Try","Critical"}]

(* --------------------------------------------------------------------------- *)
(* Initialization *)
Init ==
    /\ TypeInvariant
    /\ x = 0
    /\ y = 0
    /\ \A i \in 1..N : b[i] = FALSE
    /\ \A i \in 1..N : ctrl[i] = "Idle"

(* --------------------------------------------------------------------------- *)
(* Actions for process i *)
TRY_ENTRY(i) ==
    /\ ctrl[i] = "Idle"
    /\ b'[i]   = TRUE
    /\ ctrl'[i]= "Try"

ENTER_CS(i) ==
    /\ ctrl[i] = "Try"
    /\ \A j \in 1..N : (j # i) => ~b[j]
    /\ ctrl'[i] = "Critical"

EXIT_CS(i) ==
    /\ ctrl[i] = "Critical"
    /\ b'[i]   = FALSE
    /\ ctrl'[i]= "Idle"

(* --------------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \E i \in 1..N : (TRY_ENTRY(i) \/ ENTER_CS(i) \/ EXIT_CS(i))

(* --------------------------------------------------------------------------- *)
(* Safety invariant: no two processes in CS simultaneously *)
NoTwoCritical ==
    \A i,j \in 1..N :
        (i # j) => ~(ctrl[i] = "Critical" /\ ctrl[j] = "Critical")

(* --------------------------------------------------------------------------- *)
(* Specification *)
Spec ==
    Init
    /\ [][Next]
    /\ WF_vars(Next)
    /\ [] NoTwoCritical
    /\ []<> (\E i \in 1..N : ctrl[i] = "Critical")

END MODULE