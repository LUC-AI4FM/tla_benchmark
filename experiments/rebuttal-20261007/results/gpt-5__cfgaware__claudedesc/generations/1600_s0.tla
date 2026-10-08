---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANT N

(*
  Lamport's Fast Mutual Exclusion algorithm for processes 1..N.
  Shared variables: x (last writer), y (winner, initialized to 0), b (Boolean flags).
  Per-process locals: j (loop counter), failed (indicates losing the race).
*)

defaultInitValue == 0

Proc == 1..N

PCVals == {"A", "B", "Bwait", "D", "F", "H", "I", "G", "CS", "Exit"}

VARIABLES
  x,                 \* in 0..N
  y,                 \* in 0..N, winner register
  b,                 \* [Proc -> BOOLEAN], flags
  pc,                \* [Proc -> PCVals], control locations
  j,                 \* [Proc -> 1..(N+1)], loop counter
  failed             \* [Proc -> BOOLEAN], lost-race flag

Vars == << x, y, b, pc, j, failed >>

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCVals]
  /\ j \in [Proc -> 1..(N+1)]
  /\ failed \in [Proc -> BOOLEAN]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "A"]
  /\ j = [i \in Proc |-> 1]
  /\ failed = [i \in Proc |-> FALSE]

\* Per-process step relation
ProcStep(i) ==
  \* Start: raise flag and claim x
  \/ /\ pc[i] = "A"
     /\ x' = i
     /\ b' = [b EXCEPT ![i] = TRUE]
     /\ pc' = [pc EXCEPT ![i] = "B"]
     /\ UNCHANGED << y, j, failed >>

  \* If y != 0 then back off: drop flag and wait for y=0
  \/ /\ pc[i] = "B" /\ y # 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "Bwait"]
     /\ UNCHANGED << x, y, j, failed >>

  \* If y = 0 then try to write y := i
  \/ /\ pc[i] = "B" /\ y = 0
     /\ y' = i
     /\ pc' = [pc EXCEPT ![i] = "D"]
     /\ UNCHANGED << x, b, j, failed >>

  \* Await y = 0, then retry
  \/ /\ pc[i] = "Bwait" /\ y = 0
     /\ pc' = [pc EXCEPT ![i] = "A"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* After writing y: if someone else wrote x last, clear flag and prepare to scan flags
  \/ /\ pc[i] = "D" /\ x # i
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ j' = [j EXCEPT ![i] = 1]
     /\ pc' = [pc EXCEPT ![i] = "F"]
     /\ UNCHANGED << x, y, failed >>

  \* If still last writer of x, proceed to decision
  \/ /\ pc[i] = "D" /\ x = i
     /\ pc' = [pc EXCEPT ![i] = "G"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* Scan loop: done when j > N
  \/ /\ pc[i] = "F" /\ j[i] > N
     /\ pc' = [pc EXCEPT ![i] = "H"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* Scan loop: skip self
  \/ /\ pc[i] = "F" /\ j[i] <= N /\ j[i] = i
     /\ j' = [j EXCEPT ![i] = @ + 1]
     /\ pc' = [pc EXCEPT ![i] = "F"]
     /\ UNCHANGED << x, y, b, failed >>

  \* Scan loop: wait until b[j] = FALSE, then advance j
  \/ /\ pc[i] = "F" /\ j[i] <= N /\ j[i] # i /\ b[j[i]] = FALSE
     /\ j' = [j EXCEPT ![i] = @ + 1]
     /\ pc' = [pc EXCEPT ![i] = "F"]
     /\ UNCHANGED << x, y, b, failed >>

  \* After scan: if y != i then must wait for y=0 and mark failed
  \/ /\ pc[i] = "H" /\ y # i
     /\ pc' = [pc EXCEPT ![i] = "I"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* After scan: if y = i then can proceed to decision
  \/ /\ pc[i] = "H" /\ y = i
     /\ pc' = [pc EXCEPT ![i] = "G"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* Await y = 0 then declare failure
  \/ /\ pc[i] = "I" /\ y = 0
     /\ failed' = [failed EXCEPT ![i] = TRUE]
     /\ pc' = [pc EXCEPT ![i] = "G"]
     /\ UNCHANGED << x, y, b, j >>

  \* Decision: if not failed, enter CS
  \/ /\ pc[i] = "G" /\ failed[i] = FALSE
     /\ pc' = [pc EXCEPT ![i] = "CS"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* Decision: if failed, skip CS and go to exit
  \/ /\ pc[i] = "G" /\ failed[i] = TRUE
     /\ pc' = [pc EXCEPT ![i] = "Exit"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* Critical section (modeled as one atomic step)
  \/ /\ pc[i] = "CS"
     /\ pc' = [pc EXCEPT ![i] = "Exit"]
     /\ UNCHANGED << x, y, b, j, failed >>

  \* Exit: clear y and flag, reset failure, loop
  \/ /\ pc[i] = "Exit"
     /\ y' = 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ failed' = [failed EXCEPT ![i] = FALSE]
     /\ j' = [j EXCEPT ![i] = 1]
     /\ pc' = [pc EXCEPT ![i] = "A"]
     /\ UNCHANGED x

Next == \E i \in Proc : ProcStep(i)

\* Mutual exclusion: at most one process in CS with failed = FALSE
InCS(i) == pc[i] = "CS" /\ failed[i] = FALSE
SomeoneInCS == \E i \in Proc : InCS(i)
Contention == \E i, j \in Proc : i # j /\ b[i] /\ b[j]

Invariant ==
  \A i, j \in Proc : (i # j) => ~(InCS(i) /\ InCS(j))

Liveness == []<>(SomeoneInCS)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A i \in Proc : WF_Vars(ProcStep(i))

====