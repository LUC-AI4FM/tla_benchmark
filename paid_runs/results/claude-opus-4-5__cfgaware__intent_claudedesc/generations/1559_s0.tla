---------------------------- MODULE MutualExclusionBridge ----------------------------

EXTENDS Integers, TLC

CONSTANT Procs

VARIABLES pc, turn, flag, hist, stutter

vars == <<pc, turn, flag, hist, stutter>>

-----------------------------------------------------------------------------
(* Type correctness for all variables *)

TypeOKHS ==
    /\ pc \in [Procs -> {"idle", "entry", "entry1", "entry2", "entry3", "cs", "exit"}]
    /\ turn \in Procs \cup {0}
    /\ flag \in [Procs -> BOOLEAN]
    /\ hist \in Procs \cup {0}
    /\ stutter \in [Procs -> 0..3]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ turn = 0
    /\ flag = [p \in Procs |-> FALSE]
    /\ hist = 0
    /\ stutter = [p \in Procs |-> 0]

-----------------------------------------------------------------------------
(* Helper function: other process *)

Other(p) == CHOOSE q \in Procs : q # p

-----------------------------------------------------------------------------
(* Actions for the extended lock with stuttering *)

(* Process wants to enter - begins entry sequence *)
BeginEntry(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "entry1"]
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ stutter' = [stutter EXCEPT ![p] = 1]
    /\ UNCHANGED <<turn, hist>>

(* Entry step 2: set turn to other process *)
Entry2(p) ==
    /\ pc[p] = "entry1"
    /\ stutter[p] = 1
    /\ pc' = [pc EXCEPT ![p] = "entry2"]
    /\ turn' = Other(p)
    /\ hist' = p
    /\ stutter' = [stutter EXCEPT ![p] = 2]
    /\ UNCHANGED <<flag>>

(* Entry step 3: check condition to enter CS *)
Entry3(p) ==
    /\ pc[p] = "entry2"
    /\ stutter[p] = 2
    /\ \/ flag[Other(p)] = FALSE
       \/ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ stutter' = [stutter EXCEPT ![p] = 3]
    /\ UNCHANGED <<turn, flag, hist>>

(* Wait in entry if condition not satisfied *)
EntryWait(p) ==
    /\ pc[p] = "entry2"
    /\ stutter[p] = 2
    /\ flag[Other(p)] = TRUE
    /\ turn # p
    /\ UNCHANGED vars

(* Exit critical section *)
Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ stutter' = [stutter EXCEPT ![p] = 0]
    /\ UNCHANGED <<turn, flag, hist>>

(* Complete exit and return to idle *)
CompleteExit(p) ==
    /\ pc[p] = "exit"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn, hist, stutter>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \E p \in Procs :
        \/ BeginEntry(p)
        \/ Entry2(p)
        \/ Entry3(p)
        \/ EntryWait(p)
        \/ Exit(p)
        \/ CompleteExit(p)

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(BeginEntry(p))
        /\ WF_vars(Entry2(p))
        /\ WF_vars(Entry3(p))
        /\ WF_vars(Exit(p))
        /\ WF_vars(CompleteExit(p))

-----------------------------------------------------------------------------
(* Full specification with history and stuttering variables *)

SpecHS == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

(* Mutual exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Invariant relating pc positions, auxiliary variables to turn ownership *)
InvHS ==
    /\ MutualExclusion
    /\ \A p \in Procs :
        /\ (pc[p] = "entry2" /\ stutter[p] = 2) => flag[p] = TRUE
        /\ (pc[p] = "cs") => flag[p] = TRUE
        /\ (pc[p] = "idle") => (flag[p] = FALSE /\ stutter[p] = 0)
    /\ (hist # 0) => (turn = Other(hist))
    /\ \A p \in Procs :
        (pc[p] \in {"entry2", "cs"} /\ pc[Other(p)] \in {"entry2", "cs"}) =>
            (hist # 0 /\ turn \in Procs)

(* Lock invariant for the basic mutual exclusion property *)
LockInv ==
    /\ MutualExclusion
    /\ \A p \in Procs :
        (pc[p] = "cs") => flag[p] = TRUE

-----------------------------------------------------------------------------
(* Refinement mappings *)

(* Base lock specification (simple two-process lock) *)
(* Maps extended pc to simple lock states *)

SimplePc ==
    [p \in Procs |->
        CASE pc[p] = "idle" -> "idle"
          [] pc[p] \in {"entry1", "entry2"} -> "entry"
          [] pc[p] = "cs" -> "cs"
          [] pc[p] = "exit" -> "exit"
          [] OTHER -> pc[p]]

(* Simple lock specification *)
SimpleInit ==
    /\ SimplePc = [p \in Procs |-> "idle"]

SimpleNext ==
    \E p \in Procs :
        \/ /\ SimplePc[p] = "idle"
           /\ SimplePc' = [SimplePc EXCEPT ![p] = "entry"]
        \/ /\ SimplePc[p] = "entry"
           /\ \A q \in Procs : q # p => SimplePc[q] # "cs"
           /\ SimplePc' = [SimplePc EXCEPT ![p] = "cs"]
        \/ /\ SimplePc[p] = "cs"
           /\ SimplePc' = [SimplePc EXCEPT ![p] = "exit"]
        \/ /\ SimplePc[p] = "exit"
           /\ SimplePc' = [SimplePc EXCEPT ![p] = "idle"]

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Peterson's specification refinement *)

(* Map our pc and stutter to Peterson's labels *)
PetersonPc ==
    [p \in Procs |->
        CASE pc[p] = "idle" -> "ncs"
          [] pc[p] = "entry1" /\ stutter[p] = 1 -> "e1"
          [] pc[p] = "entry2" /\ stutter[p] = 2 -> "e2"
          [] pc[p] = "cs" -> "cs"
          [] pc[p] = "exit" -> "e3"
          [] OTHER -> "ncs"]

(* Peterson's variables mapped from our state *)
PetersonFlag == flag
PetersonTurn == IF turn = 0 THEN 1 ELSE turn

(* Peterson's specification (for reference) *)
PetersonInit ==
    /\ PetersonPc = [p \in Procs |-> "ncs"]
    /\ PetersonFlag = [p \in Procs |-> FALSE]

PetersonNext ==
    \E p \in Procs :
        LET other == Other(p) IN
        \/ /\ PetersonPc[p] = "ncs"
           /\ PetersonPc' = [PetersonPc EXCEPT ![p] = "e1"]
           /\ PetersonFlag' = [PetersonFlag EXCEPT ![p] = TRUE]
           /\ UNCHANGED PetersonTurn
        \/ /\ PetersonPc[p] = "e1"
           /\ PetersonPc' = [PetersonPc EXCEPT ![p] = "e2"]
           /\ PetersonTurn' = other
           /\ UNCHANGED PetersonFlag
        \/ /\ PetersonPc[p] = "e2"
           /\ \/ PetersonFlag[other] = FALSE
              \/ PetersonTurn = p
           /\ PetersonPc' = [PetersonPc EXCEPT ![p] = "cs"]
           /\ UNCHANGED <<PetersonFlag, PetersonTurn>>
        \/ /\ PetersonPc[p] = "cs"
           /\ PetersonPc' = [PetersonPc EXCEPT ![p] = "e3"]
           /\ UNCHANGED <<PetersonFlag, PetersonTurn>>
        \/ /\ PetersonPc[p] = "e3"
           /\ PetersonPc' = [PetersonPc EXCEPT ![p] = "ncs"]
           /\ PetersonFlag' = [PetersonFlag EXCEPT ![p] = FALSE]
           /\ UNCHANGED PetersonTurn

PSpec == PetersonInit /\ [][PetersonNext]_<<PetersonPc, PetersonFlag, PetersonTurn>>

=============================================================================