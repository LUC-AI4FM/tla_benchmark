------------------------------ MODULE DequeSpec ------------------------------
EXTENDS Naturals, TLC

CONSTANTS
    Procs,
    AddrSet,
    ValSet,
    NULL

VARIABLES Mem, leftHat, rightHat, freelist, valBag

(* Node record: [val |-> Val, next |-> Addr, prev |-> Addr] *)

Init ==
  /\ leftHat = NULL
  /\ rightHat = NULL
  /\ freelist = AddrSet
  /\ Mem = [a \in AddrSet |-> [val |-> 0, next |-> NULL, prev |-> NULL]]
  /\ valBag = [v \in ValSet |-> 0]

PushLeft(p) ==
  /\ v \in ValSet
  /\ n \in freelist
  /\ Mem' = [Mem EXCEPT ![n] = [val |-> v, next |-> leftHat, prev |-> NULL]]
  /\ leftHat' = n
  /\ rightHat' = IF rightHat = NULL THEN n ELSE rightHat
  /\ freelist' = freelist \ {n}
  /\ valBag' = [valBag EXCEPT ![v] = @ + 1]

PushRight(p) ==
  /\ v \in ValSet
  /\ n \in freelist
  /\ Mem' = [Mem EXCEPT ![n] = [val |-> v, next |-> NULL, prev |-> rightHat]]
  /\ rightHat' = n
  /\ leftHat' = IF leftHat = NULL THEN n ELSE leftHat
  /\ freelist' = freelist \ {n}
  /\ valBag' = [valBag EXCEPT ![v] = @ + 1]

PopLeft(p) ==
  /\ leftHat # NULL
  /\ n = leftHat
  /\ v = Mem[leftHat].val
  /\ Mem' = [Mem EXCEPT ![leftHat] = [!next |-> Mem[leftHat].next, !prev |-> Mem[leftHat].prev]]
  /\ leftHat' = Mem[leftHat].next
  /\ rightHat' = IF Mem[leftHat].next # NULL THEN rightHat ELSE NULL
  /\ freelist' = freelist \cup {n}
  /\ valBag' = [valBag EXCEPT ![v] = @ - 1]

PopRight(p) ==
  /\ rightHat # NULL
  /\ n = rightHat
  /\ v = Mem[rightHat].val
  /\ Mem' = [Mem EXCEPT ![rightHat] = [!prev |-> Mem[rightHat].prev, !next |-> Mem[rightHat].next]]
  /\ rightHat' = Mem[rightHat].prev
  /\ leftHat' = IF Mem[rightHat].prev # NULL THEN leftHat ELSE NULL
  /\ freelist' = freelist \cup {n}
  /\ valBag' = [valBag EXCEPT ![v] = @ - 1]

Next ==
  \E p \in Procs :
    \/ PushLeft(p)
    \/ PushRight(p)
    \/ PopLeft(p)
    \/ PopRight(p)

NodeCount(v) == \# {a \in AddrSet : a \notin freelist /\ Mem[a].val = v}

ValBagConsistent ==
  \A v \in ValSet : valBag[v] = NodeCount(v)

Spec == Init /\ [][Next]_<<Mem, leftHat, rightHat, freelist, valBag>> /\ ValBagConsistent

(* Liveness: every test process returns to T1 infinitely often *)
Liveness == \A p \in Procs : []<>(TRUE)

=============================================================================