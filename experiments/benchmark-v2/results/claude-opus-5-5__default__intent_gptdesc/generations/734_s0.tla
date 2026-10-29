------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 1..N

a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1] /\ a[2] < b[2])

Labels == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

VARIABLES num, flag, unread, max, nxt, pc

vars == << num, flag, unread, max, nxt, pc >>

TypeOK ==
    /\ num    \in [Procs -> Nat]
    /\ flag   \in [Procs -> BOOLEAN]
    /\ unread \in [Procs -> SUBSET Procs]
    /\ max    \in [Procs -> Nat]
    /\ nxt    \in [Procs -> Procs]
    /\ pc     \in [Procs -> Labels]

Init ==
    /\ num    = [i \in Procs |-> 0]
    /\ flag   = [i \in Procs |-> FALSE]
    /\ unread = [i \in Procs |-> {}]
    /\ max    = [i \in Procs |-> 0]
    /\ nxt    = [i \in Procs |-> 1]
    /\ pc     = [i \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << num, flag, unread, max, nxt >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ flag'   = [flag EXCEPT ![self] = TRUE]
    /\ unread' = [unread EXCEPT ![self] = Procs \ {self}]
    /\ max'    = [max EXCEPT ![self] = 0]
    /\ pc'     = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt >>

e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unread[self] # {}
         THEN /\ \E i \in unread[self] :
                   /\ max' = [max EXCEPT ![self] =
                                IF num[i] > max[self] THEN num[i] ELSE max[self]]
                   /\ unread' = [unread EXCEPT ![self] = unread[self] \ {i}]
              /\ pc' = pc
         ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
              /\ UNCHANGED << max, unread >>
    /\ UNCHANGED << num, flag, nxt >>

e3(self) ==
    /\ pc[self] = "e3"
    /\ num' = [num EXCEPT ![self] = max[self] + 1]
    /\ pc'  = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << flag, unread, max, nxt >>

e4(self) ==
    /\ pc[self] = "e4"
    /\ flag'   = [flag EXCEPT ![self] = FALSE]
    /\ unread' = [unread EXCEPT ![self] = Procs \ {self}]
    /\ pc'     = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

w1(self) ==
    /\ pc[self] = "w1"
    /\ IF unread[self] # {}
         THEN /\ \E i \in unread[self] :
                   /\ ~ flag[i]
                   /\ nxt' = [nxt EXCEPT ![self] = i]
              /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ nxt' = nxt
    /\ UNCHANGED << num, flag, unread, max >>

w2(self) ==
    /\ pc[self] = "w2"
    /\ \/ num[nxt[self]] = 0
       \/ << num[self], self >> \prec << num[nxt[self]], nxt[self] >>
    /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
    /\ pc'     = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, flag, max, nxt >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << num, flag, unread, max, nxt >>

exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

\* All steps except leaving the noncritical section (which need not happen)
pFair(self) == \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
               \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(pFair(self))

-----------------------------------------------------------------------------
(* Safety properties *)

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(* After(i, j): process i holds a nonzero ticket and process j is
   guaranteed not to enter the critical section ahead of i: either j has
   not yet chosen a ticket and will choose a larger one, or j's ticket is
   lexicographically larger and j still has to wait on i. *)
After(i, j) ==
    /\ num[i] > 0
    /\ \/ pc[j] = "ncs"
       \/ /\ pc[j] = "e1"
          /\ num[j] = 0
       \/ /\ pc[j] = "e2"
          /\ \/ i \in unread[j]
             \/ max[j] >= num[i]
       \/ /\ pc[j] = "e3"
          /\ max[j] >= num[i]
       \/ /\ pc[j] \in {"e4", "w1", "w2"}
          /\ << num[i], i >> \prec << num[j], j >>
          /\ (pc[j] \in {"w1", "w2"}) => (i \in unread[j])

TicketSafety ==
    \A i \in Procs :
        /\ (pc[i] \in {"w1", "w2"}) =>
               \A j \in (Procs \ unread[i]) \ {i} : After(i, j)
        /\ (pc[i] = "cs") => \A j \in Procs \ {i} : After(i, j)

StateInv ==
    \A i \in Procs :
        /\ (pc[i] \in {"ncs", "e1", "e2", "e3"}) => (num[i] = 0)
        /\ (pc[i] \in {"e4", "w1", "w2", "cs", "exit"}) => (num[i] # 0)
        /\ (pc[i] \in {"e2", "e3"}) => flag[i]
        /\ (pc[i] = "w2") => (nxt[i] # i)
        /\ (pc[i] \in {"e2", "w1", "w2"}) => (i \notin unread[i])
        /\ ( /\ pc[i] = "w2"
             /\ \/ (pc[nxt[i]] = "e2" /\ i \notin unread[nxt[i]])
                \/ pc[nxt[i]] = "e3" )
           => max[nxt[i]] >= num[i]

Inv == TypeOK /\ StateInv /\ TicketSafety

-----------------------------------------------------------------------------
(* Liveness properties *)

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "w1", "w2"}

DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

StarvationFreedom ==
    \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFreedom
THEOREM Spec => StarvationFreedom
=============================================================================