---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS, FiniteSets

CONSTANT N, defaultInitValue

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Procs == 1..N

(* Process locations *)
Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

(* Non-critical section - process i starts entry protocol *)
ncs(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b>>

(* Start: set b[i] to TRUE *)
start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "setx"]
    /\ UNCHANGED <<x, y>>

(* Set x to i *)
setx(i) ==
    /\ pc[i] = "setx"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "checky1"]
    /\ UNCHANGED <<y, b>>

(* Check if y = 0 *)
checky1(i) ==
    /\ pc[i] = "checky1"
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![i] = "sety"]
       ELSE pc' = [pc EXCEPT ![i] = "clearb1"]
    /\ UNCHANGED <<x, y, b>>

(* Set y to i (fast path) *)
sety(i) ==
    /\ pc[i] = "sety"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "checkx"]
    /\ UNCHANGED <<x, b>>

(* Check if x = i *)
checkx(i) ==
    /\ pc[i] = "checkx"
    /\ IF x = i
       THEN pc' = [pc EXCEPT ![i] = "cs"]
       ELSE pc' = [pc EXCEPT ![i] = "clearb2"]
    /\ UNCHANGED <<x, y, b>>

(* Clear b[i] when fast path blocked by y != 0 *)
clearb1(i) ==
    /\ pc[i] = "clearb1"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "waity1"]
    /\ UNCHANGED <<x, y>>

(* Wait for y = 0 (slow path entry) *)
waity1(i) ==
    /\ pc[i] = "waity1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y, b>>

(* Clear b[i] when x changed (interference detected) *)
clearb2(i) ==
    /\ pc[i] = "clearb2"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "waitflags"]
    /\ UNCHANGED <<x, y>>

(* Wait for all other flags to be clear *)
waitflags(i) ==
    /\ pc[i] = "waitflags"
    /\ \A j \in Procs \ {i} : b[j] = FALSE
    /\ pc' = [pc EXCEPT ![i] = "checky2"]
    /\ UNCHANGED <<x, y, b>>

(* Check if y = i after waiting for flags *)
checky2(i) ==
    /\ pc[i] = "checky2"
    /\ IF y = i
       THEN pc' = [pc EXCEPT ![i] = "cs"]
       ELSE pc' = [pc EXCEPT ![i] = "waity2"]
    /\ UNCHANGED <<x, y, b>>

(* Wait for y = 0 before retrying *)
waity2(i) ==
    /\ pc[i] = "waity2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y, b>>

(* Critical section - process exits *)
cs(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<x, y, b>>

(* Exit: clear y *)
exit(i) ==
    /\ pc[i] = "exit"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "clearb3"]
    /\ UNCHANGED <<x, b>>

(* Clear b[i] after exiting *)
clearb3(i) ==
    /\ pc[i] = "clearb3"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y>>

(* All actions for process i *)
proc(i) ==
    \/ ncs(i)
    \/ start(i)
    \/ setx(i)
    \/ checky1(i)
    \/ sety(i)
    \/ checkx(i)
    \/ clearb1(i)
    \/ waity1(i)
    \/ clearb2(i)
    \/ waitflags(i)
    \/ checky2(i)
    \/ waity2(i)
    \/ cs(i)
    \/ exit(i)
    \/ clearb3(i)

Next == \E i \in Procs : proc(i)

Fairness == \A i \in Procs : WF_vars(proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Mutual exclusion: at most one process in CS *)
MutualExclusion == \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => i = j

Invariant == MutualExclusion

(* Liveness: some process infinitely often enters CS *)
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

==========================================================================