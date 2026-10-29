------------------------------ MODULE MCBakery ------------------------------
(***************************************************************************)
(* Bounded wrapper for the Bakery algorithm.  MaxNat bounds the natural    *)
(* numbers, and NatOverride (0 .. MaxNat) replaces Nat so that the ticket  *)
(* numbers form a finite set for model checking.  The Bakery algorithm is  *)
(* included inline, parameterized by NatOverride, so this module parses on *)
(* its own.                                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

ASSUME NAssump      == N \in Nat \ {0}
ASSUME MaxNatAssump == MaxNat \in Nat

NatOverride == 0 .. MaxNat

Procs == 1 .. N

\* Lexicographic order on <<ticket, process id>> pairs
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1] /\ a[2] < b[2])

Max(a, b) == IF a >= b THEN a ELSE b

VARIABLES num, flag, unchecked, max, nxt, pc

vars == <<num, flag, unchecked, max, nxt, pc>>

TypeOK ==
  /\ num       \in [Procs -> NatOverride]
  /\ flag      \in [Procs -> BOOLEAN]
  /\ unchecked \in [Procs -> SUBSET Procs]
  /\ max       \in [Procs -> NatOverride]
  /\ nxt       \in [Procs -> Procs]
  /\ pc        \in [Procs -> {"ncs", "e1", "e2", "e3", "w1", "w2", "cs", "exit"}]

Init ==
  /\ num       = [i \in Procs |-> 0]
  /\ flag      = [i \in Procs |-> FALSE]
  /\ unchecked = [i \in Procs |-> {}]
  /\ max       = [i \in Procs |-> 0]
  /\ nxt       = [i \in Procs |-> i]
  /\ pc        = [i \in Procs |-> "ncs"]

\* Leave the noncritical section and begin choosing a ticket
ncs(i) ==
  /\ pc[i] = "ncs"
  /\ flag'      = [flag EXCEPT ![i] = TRUE]
  /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
  /\ max'       = [max EXCEPT ![i] = 0]
  /\ pc'        = [pc EXCEPT ![i] = "e1"]
  /\ UNCHANGED <<num, nxt>>

\* Read the other processes' tickets one at a time, keeping the maximum
e1(i) ==
  /\ pc[i] = "e1"
  /\ IF unchecked[i] # {}
       THEN \E j \in unchecked[i] :
              /\ max'       = [max EXCEPT ![i] = Max(max[i], num[j])]
              /\ unchecked' = [unchecked EXCEPT ![i] = unchecked[i] \ {j}]
              /\ UNCHANGED pc
       ELSE /\ pc' = [pc EXCEPT ![i] = "e2"]
            /\ UNCHANGED <<max, unchecked>>
  /\ UNCHANGED <<num, flag, nxt>>

\* Take a ticket one larger than the maximum seen (bounded by NatOverride)
e2(i) ==
  /\ pc[i] = "e2"
  /\ max[i] + 1 \in NatOverride
  /\ num' = [num EXCEPT ![i] = max[i] + 1]
  /\ pc'  = [pc EXCEPT ![i] = "e3"]
  /\ UNCHANGED <<flag, unchecked, max, nxt>>

\* Finish choosing
e3(i) ==
  /\ pc[i] = "e3"
  /\ flag'      = [flag EXCEPT ![i] = FALSE]
  /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
  /\ pc'        = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<num, max, nxt>>

\* Pick an unchecked process and wait until it is done choosing
w1(i) ==
  /\ pc[i] = "w1"
  /\ IF unchecked[i] # {}
       THEN \E j \in unchecked[i] :
              /\ ~flag[j]
              /\ nxt' = [nxt EXCEPT ![i] = j]
              /\ pc'  = [pc EXCEPT ![i] = "w2"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ UNCHANGED nxt
  /\ UNCHANGED <<num, flag, unchecked, max>>

\* Wait until the chosen process has no ticket or a larger one
w2(i) ==
  /\ pc[i] = "w2"
  /\ LET j == nxt[i] IN
       /\ \/ num[j] = 0
          \/ <<num[i], i>> \prec <<num[j], j>>
       /\ unchecked' = [unchecked EXCEPT ![i] = unchecked[i] \ {j}]
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<num, flag, max, nxt>>

\* Critical section
cs(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

\* Give up the ticket and return to the noncritical section
exit(i) ==
  /\ pc[i] = "exit"
  /\ num' = [num EXCEPT ![i] = 0]
  /\ pc'  = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED <<flag, unchecked, max, nxt>>

\* All steps of process i except leaving the noncritical section
Proc(i) == e1(i) \/ e2(i) \/ e3(i) \/ w1(i) \/ w2(i) \/ cs(i) \/ exit(i)

Next == \E i \in Procs : ncs(i) \/ Proc(i)

\* Weak fairness on every step except leaving the noncritical section
Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in Procs : WF_vars(Proc(i))

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
  \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness *)

StarvationFree ==
  \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================