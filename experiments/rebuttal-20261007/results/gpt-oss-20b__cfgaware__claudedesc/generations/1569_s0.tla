------------------------------ MODULE CBakery ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS NumProcs, MaxNum

VARIABLES num, choosing, cs

(* Type invariants *)
TypeInv == 
   /\ num \in [1..NumProcs -> Nat]
   /\ choosing \in [1..NumProcs -> BOOLEAN]
   /\ cs \subseteq 1..NumProcs

Init ==
   /\ choosing = [i \in 1..NumProcs |-> FALSE]
   /\ num = [i \in 1..NumProcs |-> 0]
   /\ cs = {}

StartChoosing(i) == 
   /\ i \in 1..NumProcs
   /\ choosing[i] = FALSE
   /\ choosing' = [choosing EXCEPT ![i] = TRUE]
   /\ num' = num
   /\ cs' = cs

FinishChoosing(i) ==
   LET
      maxTicket == 1 + \max (\seq {num[j] : j \in 1..NumProcs})
      newTicket == IF maxTicket <= MaxNum THEN maxTicket ELSE MaxNum
   IN
      /\ i \in 1..NumProcs
      /\ choosing[i] = TRUE
      /\ num' = [num EXCEPT ![i] = newTicket]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ cs' = cs

EnterCS(i) ==
   /\ i \in 1..NumProcs
   /\ num[i] > 0
   /\ i \notin cs
   /\ (\A j \in 1..NumProcs : (j # i) => (
        choosing[j] = FALSE /\
        (num[j] = 0 \/ num[j] > num[i] \/ (num[j] = num[i] /\ j > i))
     ))
   /\ cs' = cs \cup {i}
   /\ num' = num
   /\ choosing' = choosing

ExitCS(i) ==
   /\ i \in 1..NumProcs
   /\ i \in cs
   /\ cs' = cs \setminus {i}
   /\ num' = [num EXCEPT ![i] = 0]
   /\ choosing' = choosing

Next == 
   \/ \E i \in 1..NumProcs : StartChoosing(i)
   \/ \E i \in 1..NumProcs : FinishChoosing(i)
   \/ \E i \in 1..NumProcs : EnterCS(i)
   \/ \E i \in 1..NumProcs : ExitCS(i)

vars == {num, choosing, cs}

Spec == Init /\ [][Next]_vars

Invariant == (#cs <= 1)

===============================================================================