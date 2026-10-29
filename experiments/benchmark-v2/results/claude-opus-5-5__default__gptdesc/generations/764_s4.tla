--------------------------- MODULE DiningPhilosophers ---------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(***************************************************************************
--algorithm DiningPhilosophers
variables sem = [f \in 0..N-1 |-> 1];
define
  RightFork(p) == p
  LeftFork(p)  == (p + 1) % N
end define;
fair+ process Proc \in 0..N-1
begin
l1: while TRUE do
      if self = 0 then
        when sem[LeftFork(self)] = 1;
        sem[LeftFork(self)] := 0;
      else
        when sem[RightFork(self)] = 1;
        sem[RightFork(self)] := 0;
      end if;
l2:   if self = 0 then
        when sem[RightFork(self)] = 1;
        sem[RightFork(self)] := 0;
      else
        when sem[LeftFork(self)] = 1;
        sem[LeftFork(self)] := 0;
      end if;
e:    sem[RightFork(self)] := 1 || sem[LeftFork(self)] := 1;
    end while;
end process;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES sem, pc

(* define statement *)
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

vars == << sem, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ sem = [f \in 0..N-1 |-> 1]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ IF self = 0
                  THEN /\ sem[LeftFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
                  ELSE /\ sem[RightFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l2"]

l2(self) == /\ pc[self] = "l2"
            /\ IF self = 0
                  THEN /\ sem[RightFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![RightFork(self)] = 0]
                  ELSE /\ sem[LeftFork(self)] = 1
                       /\ sem' = [sem EXCEPT ![LeftFork(self)] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e"]

e(self) == /\ pc[self] = "e"
           /\ sem' = [sem EXCEPT ![RightFork(self)] = 1,
                                 ![LeftFork(self)] = 1]
           /\ pc' = [pc EXCEPT ![self] = "l1"]

Proc(self) == l1(self) \/ l2(self) \/ e(self)

Next == (\E self \in 0..N-1: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..N-1 : SF_vars(Proc(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ sem \in [0..N-1 -> {0, 1}]
          /\ pc \in [ProcSet -> {"l1", "l2", "e"}]

(* Adjacent philosophers never eat at the same time. *)
IsEating(p) == pc[p] = "e"

MutualExclusion ==
  \A p \in 0..N-1 : ~(IsEating(p) /\ IsEating((p + 1) % N))

(* Every philosopher eats infinitely often. *)
StarvationFree == \A p \in 0..N-1 : []<>(IsEating(p))

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFree
=============================================================================