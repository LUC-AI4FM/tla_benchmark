------------------------------- MODULE Peterson -------------------------------
EXTENDS Naturals

VARIABLES c, turn, pc

vars == <<c, turn, pc>>

Proc == {1, 2}

Other(p) == 3 - p

Labels == {"a0", "a1", "a2", "a3", "cs", "a4"}

-----------------------------------------------------------------------------

Init == /\ c = [p \in Proc |-> FALSE]
        /\ turn = 1
        /\ pc = [p \in Proc |-> "a0"]

a0(p) == /\ pc[p] = "a0"
         /\ pc' = [pc EXCEPT ![p] = "a1"]
         /\ UNCHANGED <<c, turn>>

a1(p) == /\ pc[p] = "a1"
         /\ c' = [c EXCEPT ![p] = TRUE]
         /\ pc' = [pc EXCEPT ![p] = "a2"]
         /\ UNCHANGED turn

a2(p) == /\ pc[p] = "a2"
         /\ turn' = Other(p)
         /\ pc' = [pc EXCEPT ![p] = "a3"]
         /\ UNCHANGED c

a3(p) == /\ pc[p] = "a3"
         /\ \/ ~ c[Other(p)]
            \/ turn = p
         /\ pc' = [pc EXCEPT ![p] = "cs"]
         /\ UNCHANGED <<c, turn>>

cs(p) == /\ pc[p] = "cs"
         /\ pc' = [pc EXCEPT ![p] = "a4"]
         /\ UNCHANGED <<c, turn>>

a4(p) == /\ pc[p] = "a4"
         /\ c' = [c EXCEPT ![p] = FALSE]
         /\ pc' = [pc EXCEPT ![p] = "a0"]
         /\ UNCHANGED turn

proc(p) == a0(p) \/ a1(p) \/ a2(p) \/ a3(p) \/ cs(p) \/ a4(p)

Next == \E p \in Proc : proc(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK == /\ c \in [Proc -> BOOLEAN]
          /\ turn \in Proc
          /\ pc \in [Proc -> Labels]

Inv == /\ \A p \in Proc : c[p] <=> (pc[p] \in {"a2", "a3", "cs", "a4"})
       /\ \A p \in Proc :
             pc[p] \in {"cs", "a4"} =>
                \/ turn = p
                \/ pc[Other(p)] \in {"a0", "a1", "a2"}
       /\ ~ (pc[1] \in {"cs", "a4"} /\ pc[2] \in {"cs", "a4"})

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract Lock specification.                  *)

pc_translation ==
   [p \in Proc |-> IF pc[p] \in {"cs", "a4"} THEN "cs" ELSE "idle"]

lock_translation ==
   IF \E p \in Proc : pc[p] \in {"cs", "a4"}
      THEN CHOOSE p \in Proc : pc[p] \in {"cs", "a4"}
      ELSE 0

LInit == /\ pc_translation = [p \in Proc |-> "idle"]
         /\ lock_translation = 0

LAcquire(p) == /\ pc_translation[p] = "idle"
               /\ lock_translation = 0
               /\ pc_translation' = [pc_translation EXCEPT ![p] = "cs"]
               /\ lock_translation' = p

LRelease(p) == /\ pc_translation[p] = "cs"
               /\ lock_translation = p
               /\ pc_translation' = [pc_translation EXCEPT ![p] = "idle"]
               /\ lock_translation' = 0

LNext == \E p \in Proc : LAcquire(p) \/ LRelease(p)

lvars == <<pc_translation, lock_translation>>

LSpec == LInit /\ [][LNext]_lvars

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => LSpec
=============================================================================