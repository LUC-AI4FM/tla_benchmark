MODULE CBakery
EXTENDS Naturals

CONSTANTS NumProcs, MaxNum

ProcSet == 1..NumProcs

(* Helper function to compute maximum of a set *)
MaxVal(S) == \E v \in S : (\A w \in S : v >= w)

VARIABLES num, choosing, read, max, nxt, cs

Init ==
    /\ num = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ read = [p \in ProcSet |-> [j \in ProcSet |-> 0]]
    /\ max = [i \in ProcSet |-> 0]
    /\ nxt = [i \in ProcSet |-> 0]
    /\ cs = [i \in ProcSet |-> FALSE]

StartIteration(p) ==
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<num, read, max, nxt, cs>>

ScanTickets(p) ==
    /\ read' = [read EXCEPT ![p] = [i \in ProcSet |-> num[i]]]
    /\ UNCHANGED <<num, choosing, max, nxt, cs>>

ComputeMax(p) ==
    /\ max' = [max EXCEPT ![p] = MaxVal({num[i] : i \in ProcSet})]
    /\ UNCHANGED <<num, choosing, read, nxt, cs>>

SetNxt(p) ==
    /\ nxt' = [nxt EXCEPT ![p] = max[p] + 1]
    /\ UNCHANGED <<num, choosing, read, max, cs>>

ClearChoosing(p) ==
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<num, read, max, nxt, cs>>

EnterCS(p) ==
    /\ \A q \in ProcSet : (q # p) => NOT choosing[q] /\ (num[q] = 0 \/ num[q] > nxt[p] \/ (num[q] = nxt[p] /\ q > p))
    /\ NOT cs[p]
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<num, choosing, read, max, nxt>>

ExitCS(p) ==
    /\ cs[p]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ num' = [num EXCEPT ![p] = 0]
    /\ UNCHANGED <<choosing, read, max, nxt>>

Next == \E p \in ProcSet :
          (StartIteration(p) \/ ScanTickets(p) \/ ComputeMax(p) \/ SetNxt(p) \/ ClearChoosing(p) \/ EnterCS(p) \/ ExitCS(p))

TicketBound == \A i \in ProcSet : num[i] <= MaxNum

MutualExclusion == \A i,j \in ProcSet : (i # j) => ~(cs[i] /\ cs[j])

Spec == Init /\ [][Next]_(num, choosing, read, max, nxt, cs) /\ []TicketBound /\ []MutualExclusion

============================================================================