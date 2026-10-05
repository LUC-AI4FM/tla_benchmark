---------------------------- MODULE Bakery ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NumProcs, MaxNum

Proc == 1..NumProcs

VARIABLES num, choosing, pc, read, max, nxt

vars == <<num, choosing, pc, read, max, nxt>>

Init ==
    /\ num = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ pc = [i \in Proc |-> "loop"]
    /\ read = [i \in Proc |-> 1]
    /\ max = [i \in Proc |-> 0]
    /\ nxt = [i \in Proc |-> 1]

(* Choosing phase: loop - start choosing *)
loop(i) ==
    /\ pc[i] = "loop"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ max' = [max EXCEPT ![i] = 0]
    /\ read' = [read EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "d1"]
    /\ UNCHANGED <<num, nxt>>

(* Choosing phase: d1 - scan to find max *)
d1(i) ==
    /\ pc[i] = "d1"
    /\ IF read[i] <= NumProcs
       THEN /\ pc' = [pc EXCEPT ![i] = "d2"]
            /\ UNCHANGED <<num, choosing, read, max, nxt>>
       ELSE /\ pc' = [pc EXCEPT ![i] = "d3"]
            /\ UNCHANGED <<num, choosing, read, max, nxt>>

(* Choosing phase: d2 - update max if needed *)
d2(i) ==
    /\ pc[i] = "d2"
    /\ IF num[read[i]] > max[i]
       THEN max' = [max EXCEPT ![i] = num[read[i]]]
       ELSE max' = max
    /\ read' = [read EXCEPT ![i] = read[i] + 1]
    /\ pc' = [pc EXCEPT ![i] = "d1"]
    /\ UNCHANGED <<num, choosing, nxt>>

(* Choosing phase: d3 - assign ticket and clear choosing *)
d3(i) ==
    /\ pc[i] = "d3"
    /\ num' = [num EXCEPT ![i] = max[i] + 1]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ nxt' = [nxt EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<read, max>>

(* Waiting phase: w1 - wait for process nxt to stop choosing *)
w1(i) ==
    /\ pc[i] = "w1"
    /\ IF nxt[i] <= NumProcs
       THEN IF nxt[i] = i
            THEN /\ nxt' = [nxt EXCEPT ![i] = nxt[i] + 1]
                 /\ pc' = pc
                 /\ UNCHANGED <<num, choosing, read, max>>
            ELSE IF ~choosing[nxt[i]]
                 THEN /\ pc' = [pc EXCEPT ![i] = "w2"]
                      /\ UNCHANGED <<num, choosing, read, max, nxt>>
                 ELSE UNCHANGED vars
       ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ UNCHANGED <<num, choosing, read, max, nxt>>

(* Waiting phase: w2 - check priority against process nxt *)
w2(i) ==
    /\ pc[i] = "w2"
    /\ \/ num[nxt[i]] = 0
       \/ num[nxt[i]] > num[i]
       \/ (num[nxt[i]] = num[i] /\ nxt[i] > i)
    /\ nxt' = [nxt EXCEPT ![i] = nxt[i] + 1]
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<num, choosing, read, max>>

(* Critical section *)
cs(i) ==
    /\ pc[i] = "cs"
    /\ num' = [num EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "loop"]
    /\ UNCHANGED <<choosing, read, max, nxt>>

Step(i) ==
    \/ loop(i)
    \/ d1(i)
    \/ d2(i)
    \/ d3(i)
    \/ w1(i)
    \/ w2(i)
    \/ cs(i)

Next == \E i \in Proc : Step(i)

Spec == Init /\ [][Next]_vars

(* Mutual exclusion invariant *)
Invariant ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* State constraint for model checking *)
Constraint ==
    \A i \in Proc : num[i] <= MaxNum

(* Predicates for possible state counts *)
InCS == \E i \in Proc : pc[i] = "cs"

ChooseNumber == \E i \in Proc : choosing[i] = TRUE

PossibleCounts ==
    /\ InCS
    /\ ChooseNumber

=======================================================================