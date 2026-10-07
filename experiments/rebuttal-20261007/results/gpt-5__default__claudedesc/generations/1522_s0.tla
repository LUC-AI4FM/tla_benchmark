------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Integers, Sequences

CONSTANTS Procs, Leader, MaxK

(***************************************************************************)
(* Dyadic weights are represented as records [num, k] denoting             *)
(* the value num / 2^k, with k bounded by MaxK.                            *)
(***************************************************************************)

Weight == [num: Nat, k: 0..MaxK]

ZeroW == [num |-> 0, k |-> 0]
OneW  == [num |-> 1, k |-> 0]

KMax(a, b) == IF a < b THEN b ELSE a

AddW(a, b) ==
  LET km == KMax(a.k, b.k)
  IN [ num |-> a.num * (2 ^ (km - a.k)) + b.num * (2 ^ (km - b.k)),
       k   |-> km ]

Half(w) == [num |-> w.num, k |-> w.k + 1]

RECURSIVE SumSeq(_, _)
SumSeq(s, K) ==
  IF Len(s) = 0
    THEN 0
    ELSE s[1].num * (2 ^ (K - s[1].k)) + SumSeq(Tail(s), K)

RECURSIVE SumSet(_)
SumSet(S) ==
  IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN x + SumSet(S \ {x})

TotalAtK(K) ==
  LET perProc ==
        { w[p].num * (2 ^ (K - w[p].k)) + SumSeq(q[p], K) : p \in Procs }
  IN  SumSet(perProc)

NonLdr == Procs \ {Leader}

VARIABLES active, w, q

vars == << active, w, q >>

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ Leader \in Procs
  /\ MaxK \in Nat
  /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
  /\ w = [p \in Procs |-> IF p = Leader THEN OneW ELSE ZeroW]
  /\ q = [p \in Procs |-> << >>]

(***************************************************************************)
(* State constraints and type/weight invariants                            *)
(***************************************************************************)

StateConstraint ==
  /\ \A p \in Procs : w[p].k \in 0..MaxK
  /\ \A p \in Procs : \A i \in 1..Len(q[p]) : q[p][i].k \in 0..MaxK

TypeOK ==
  /\ Leader \in Procs
  /\ MaxK \in Nat
  /\ active \in [Procs -> BOOLEAN]
  /\ w \in [Procs -> Weight]
  /\ q \in [Procs -> Seq(Weight)]
  /\ TotalAtK(MaxK) = 2 ^ MaxK

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Send(p, d) ==
  /\ p \in Procs
  /\ d \in Procs
  /\ d # p
  /\ active[p]
  /\ w[p].num > 0
  /\ w[p].k < MaxK
  /\ LET h == Half(w[p])
     IN  /\ w' = [w EXCEPT ![p] = h]
         /\ q' = [q EXCEPT ![d] = Append(q[d], h)]
         /\ active' = active

Idle(p) ==
  /\ p \in NonLdr
  /\ active[p]
  /\ LET msg == w[p]
     IN  /\ w' = [w EXCEPT ![p] = ZeroW]
         /\ q' = [q EXCEPT ![Leader] = Append(q[Leader], msg)]
         /\ active' = [active EXCEPT ![p] = FALSE]

Rcv(p) ==
  /\ p \in NonLdr
  /\ Len(q[p]) > 0
  /\ LET m == Head(q[p])
     IN  /\ w' = [w EXCEPT ![p] = AddW(w[p], m)]
         /\ q' = [q EXCEPT ![p] = Tail(q[p])]
         /\ active' = [active EXCEPT ![p] = TRUE]

RcvLdr ==
  /\ Len(q[Leader]) > 0
  /\ LET m == Head(q[Leader])
     IN  /\ w' = [w EXCEPT ![Leader] = AddW(w[Leader], m)]
         /\ q' = [q EXCEPT ![Leader] = Tail(q[Leader])]
         /\ active' = active

IdleLdr ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ w' = w
  /\ q' = q

Next ==
  \/ \E p \in Procs : \E d \in Procs \ {p} : Send(p, d)
  \/ \E p \in NonLdr : Rcv(p)
  \/ \E p \in NonLdr : Idle(p)
  \/ RcvLdr
  \/ IdleLdr

(***************************************************************************)
(* Fairness                                                                *)
(***************************************************************************)

Fair ==
  /\ WF_vars(RcvLdr)
  /\ WF_vars(IdleLdr)
  /\ \A p \in NonLdr : WF_vars(Rcv(p))
  /\ \A p \in NonLdr : WF_vars(Idle(p))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fair
  /\ []StateConstraint

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

IsOne(wgt) == wgt.num * (2 ^ (MaxK - wgt.k)) = 2 ^ MaxK

Detected ==
  /\ ~active[Leader]
  /\ IsOne(w[Leader])

Terminated ==
  /\ \A p \in Procs : ~active[p]
  /\ \A p \in Procs : Len(q[p]) = 0

Safe == [](Detected => []Terminated)
Live == (Terminated) ~> Detected

THEOREM Spec => []TypeOK
THEOREM Spec => Safe
THEOREM Spec => Live

=============================================================================