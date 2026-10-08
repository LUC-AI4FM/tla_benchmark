----------------------------- MODULE CBakery -----------------------------
EXTENDS Naturals, TLC

CONSTANTS NumProcs, MaxNum

Procs == 1..NumProcs

VARIABLES pc, num, choosing, read, max, nxt

vars == << pc, num, choosing, read, max, nxt >>

Init ==
  /\ pc = [p \in Procs |-> "d1"]
  /\ num = [p \in Procs |-> 0]
  /\ choosing = [p \in Procs |-> FALSE]
  /\ read = [p \in Procs |-> 0]
  /\ max = [p \in Procs |-> 0]
  /\ nxt = [p \in Procs |-> 0]

IsAhead(p, q) ==
  (num[q] = 0)
  \/ (num[q] > num[p])
  \/ ((num[q] = num[p]) /\ (q > p))

d1(p) ==
  /\ pc[p] = "d1"
  /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  /\ max' = [max EXCEPT ![p] = 0]
  /\ read' = [read EXCEPT ![p] = 1]
  /\ pc' = [pc EXCEPT ![p] = "d2"]
  /\ UNCHANGED << num, nxt >>

d2scan(p) ==
  /\ pc[p] = "d2"
  /\ read[p] <= NumProcs
  /\ max' = [max EXCEPT ![p] =
                IF num[read[p]] > max[p] THEN num[read[p]] ELSE max[p]]
  /\ read' = [read EXCEPT ![p] = read[p] + 1]
  /\ UNCHANGED << pc, choosing, num, nxt >>

d2finish(p) ==
  /\ pc[p] = "d2"
  /\ read[p] > NumProcs
  /\ nxt' = [nxt EXCEPT ![p] = max[p] + 1]
  /\ num' = [num EXCEPT ![p] = max[p] + 1]
  /\ pc' = [pc EXCEPT ![p] = "d3"]
  /\ UNCHANGED << choosing, read, max >>

d3(p) ==
  /\ pc[p] = "d3"
  /\ choosing' = [choosing EXCEPT ![p] = FALSE]
  /\ read' = [read EXCEPT ![p] = 1]
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED << num, max, nxt >>

w1skipself(p) ==
  /\ pc[p] = "w1"
  /\ read[p] <= NumProcs
  /\ read[p] = p
  /\ read' = [read EXCEPT ![p] = read[p] + 1]
  /\ UNCHANGED << pc, choosing, num, max, nxt >>

w1goW2(p) ==
  /\ pc[p] = "w1"
  /\ read[p] <= NumProcs
  /\ read[p] # p
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ UNCHANGED << choosing, num, read, max, nxt >>

enterCS(p) ==
  /\ pc[p] = "w1"
  /\ read[p] > NumProcs
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << choosing, num, read, max, nxt >>

w2ok(p) ==
  /\ pc[p] = "w2"
  /\ LET q == read[p] IN
       /\ choosing[q] = FALSE
       /\ IsAhead(p, q)
  /\ read' = [read EXCEPT ![p] = read[p] + 1]
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED << choosing, num, max, nxt >>

exitCS(p) ==
  /\ pc[p] = "cs"
  /\ num' = [num EXCEPT ![p] = 0]
  /\ pc' = [pc EXCEPT ![p] = "d1"]
  /\ UNCHANGED << choosing, read, max, nxt >>

Next ==
  \E p \in Procs:
       d1(p)
    \/ d2scan(p)
    \/ d2finish(p)
    \/ d3(p)
    \/ w1skipself(p)
    \/ w1goW2(p)
    \/ enterCS(p)
    \/ w2ok(p)
    \/ exitCS(p)

Spec == Init /\ [][Next]_vars

Invariant ==
  \A p \in Procs: \A q \in Procs:
    (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")
=============================================================================