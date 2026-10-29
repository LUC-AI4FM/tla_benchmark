------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssump == N \in Nat \ {0}

Procs == 1..N

(* Lexicographic order on pairs <<token, process id>> *)
a \prec b == \/ a[1] < b[1]
             \/ /\ a[1] = b[1]
                /\ a[2] < b[2]

VARIABLES num,     \* num[p]   : shared token register of process p
          flag,    \* flag[p]  : shared announcement flag of process p
          pc,      \* pc[p]    : control location of process p
          unread,  \* unread[p]: processes p has not yet read in this phase
          max,     \* max[p]   : largest token p has read so far
          nxt      \* nxt[p]   : process p is currently waiting on

vars == <<num, flag, pc, unread, max, nxt>>

Labels == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

TypeOK == /\ num    \in [Procs -> Nat]
          /\ flag   \in [Procs -> BOOLEAN]
          /\ pc     \in [Procs -> Labels]
          /\ unread \in [Procs -> SUBSET Procs]
          /\ max    \in [Procs -> Nat]
          /\ nxt    \in [Procs -> Procs]

Init == /\ num    = [i \in Procs |-> 0]
        /\ flag   = [i \in Procs |-> FALSE]
        /\ pc     = [i \in Procs |-> "ncs"]
        /\ unread = [i \in Procs |-> {}]
        /\ max    = [i \in Procs |-> 0]
        /\ nxt    = [i \in Procs |-> 1]

-----------------------------------------------------------------------------
(* Noncritical section: the process may stay here forever (no fairness).   *)
ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED <<num, flag, unread, max, nxt>>

(* Announce intent.  The flag may flicker (non-atomic register write).      *)
e1Flip(self) == /\ pc[self] = "e1"
                /\ flag' = [flag EXCEPT ![self] = ~ @]
                /\ UNCHANGED <<num, pc, unread, max, nxt>>

e1Go(self) == /\ pc[self] = "e1"
              /\ flag'   = [flag EXCEPT ![self] = TRUE]
              /\ unread' = [unread EXCEPT ![self] = Procs \ {self}]
              /\ max'    = [max EXCEPT ![self] = 0]
              /\ pc'     = [pc EXCEPT ![self] = "e2"]
              /\ UNCHANGED <<num, nxt>>

(* Read the other processes' tokens one at a time, in any order.           *)
e2(self) == /\ pc[self] = "e2"
            /\ IF unread[self] # {}
                 THEN /\ \E i \in unread[self] :
                           /\ unread' = [unread EXCEPT ![self] = @ \ {i}]
                           /\ max' = [max EXCEPT ![self] =
                                        IF num[i] > @ THEN num[i] ELSE @]
                      /\ UNCHANGED pc
                 ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                      /\ UNCHANGED <<unread, max>>
            /\ UNCHANGED <<num, flag, nxt>>

(* Choose a token.  Intermediate (unreliable) writes of arbitrary values.  *)
e3Flip(self) == /\ pc[self] = "e3"
                /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
                /\ UNCHANGED <<flag, pc, unread, max, nxt>>

e3Go(self) == /\ pc[self] = "e3"
              /\ \E k \in {j \in Nat : j > max[self]} :
                    num' = [num EXCEPT ![self] = k]
              /\ pc' = [pc EXCEPT ![self] = "e4"]
              /\ UNCHANGED <<flag, unread, max, nxt>>

(* Lower the flag (may flicker before settling).                            *)
e4Flip(self) == /\ pc[self] = "e4"
                /\ flag' = [flag EXCEPT ![self] = ~ @]
                /\ UNCHANGED <<num, pc, unread, max, nxt>>

e4Go(self) == /\ pc[self] = "e4"
              /\ flag'   = [flag EXCEPT ![self] = FALSE]
              /\ unread' = [unread EXCEPT ![self] = Procs \ {self}]
              /\ pc'     = [pc EXCEPT ![self] = "w1"]
              /\ UNCHANGED <<num, max, nxt>>

(* Wait: pick an unchecked process, wait for its flag to be down ...        *)
w1(self) == /\ pc[self] = "w1"
            /\ IF unread[self] # {}
                 THEN \E i \in unread[self] :
                         /\ ~ flag[i]
                         /\ nxt' = [nxt EXCEPT ![self] = i]
                         /\ pc'  = [pc EXCEPT ![self] = "w2"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ UNCHANGED nxt
            /\ UNCHANGED <<num, flag, unread, max>>

(* ... then wait until it is not ahead of us in the (token, id) order.      *)
w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unread' = [unread EXCEPT ![self] = @ \ {nxt[self]}]
            /\ pc'     = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, flag, max, nxt>>

(* Critical section                                                         *)
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<num, flag, unread, max, nxt>>

(* Exit: reset token, possibly via intermediate arbitrary writes.          *)
exitFlip(self) == /\ pc[self] = "exit"
                  /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
                  /\ UNCHANGED <<flag, pc, unread, max, nxt>>

exitGo(self) == /\ pc[self] = "exit"
                /\ num' = [num EXCEPT ![self] = 0]
                /\ pc'  = [pc EXCEPT ![self] = "ncs"]
                /\ UNCHANGED <<flag, unread, max, nxt>>

(* All steps of a process other than leaving the noncritical section       *)
pStep(self) == \/ e1Flip(self) \/ e1Go(self)
               \/ e2(self)
               \/ e3Flip(self) \/ e3Go(self)
               \/ e4Flip(self) \/ e4Go(self)
               \/ w1(self) \/ w2(self)
               \/ cs(self)
               \/ exitFlip(self) \/ exitGo(self)

p(self) == ncs(self) \/ pStep(self)

Next == \E self \in Procs : p(self)

(* Weak fairness for enabled process steps (outside the noncritical         *)
(* section), and weak fairness ensuring nondeterministic flickering writes  *)
(* eventually settle.                                                       *)
Fairness == \A self \in Procs :
               /\ WF_vars(pStep(self))
               /\ WF_vars(e1Go(self))
               /\ WF_vars(e3Go(self))
               /\ WF_vars(e4Go(self))
               /\ WF_vars(exitGo(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: mutual exclusion                                                 *)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(* Ordering-based precedence: i is guaranteed to precede j                  *)
Before(i, j) ==
    /\ num[i] > 0
    /\ \/ pc[j] \in {"ncs", "e1", "exit"}
       \/ /\ pc[j] = "e2"
          /\ \/ i \in unread[j]
             \/ max[j] >= num[i]
       \/ /\ pc[j] = "e3"
          /\ max[j] >= num[i]
       \/ /\ pc[j] \in {"e4", "w1", "w2"}
          /\ <<num[i], i>> \prec <<num[j], j>>
          /\ (pc[j] \in {"w1", "w2"}) => (i \in unread[j])

(* Inductive invariant implying mutual exclusion                            *)
Inv == \A i \in Procs :
         /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
         /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
         /\ (pc[i] \in {"e2", "e3"}) => flag[i]
         /\ (pc[i] = "w2") => (nxt[i] # i)
         /\ (pc[i] \in {"e2", "w1", "w2"}) => (i \notin unread[i])
         /\ (pc[i] \in {"w1", "w2"}) =>
               \A j \in (Procs \ unread[i]) \ {i} : Before(i, j)
         /\ ( /\ pc[i] = "w2"
              /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unread[nxt[i]])
                 \/ pc[nxt[i]] = "e3" )
            => (max[nxt[i]] >= num[i])
         /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)

FullInv == TypeOK /\ Inv

THEOREM Spec => [](TypeOK /\ Inv /\ MutualExclusion)

-----------------------------------------------------------------------------
(* Liveness                                                                 *)
Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "w1", "w2"}
InCS(i)   == pc[i] = "cs"

(* Starvation-freedom: every process that begins the entry protocol         *)
(* eventually enters its critical section.                                  *)
StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> InCS(i)

(* Deadlock-freedom: if some process is trying, some process eventually     *)
(* enters the critical section.                                             *)
DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))

THEOREM Spec => StarvationFree /\ DeadlockFree
=============================================================================