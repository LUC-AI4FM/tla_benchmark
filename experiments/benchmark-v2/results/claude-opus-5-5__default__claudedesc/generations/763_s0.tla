---------------------------- MODULE ApaDiningPhilosophers ----------------------------
(***************************************************************************)
(* Apalache-compatible, type-annotated Dining Philosophers specification.  *)
(*                                                                         *)
(* The original setup imports Init and Next from a separate               *)
(* DiningPhilosophers module via INSTANCE. That module may not be present  *)
(* for SANY, so this module defines the same state machine itself. It      *)
(* keeps the same constant NP and the variables forks, pc and hungry.      *)
(*                                                                         *)
(* The original specification has weak fairness for each philosopher's    *)
(* actions, quantified over philosophers. Apalache cannot handle that      *)
(* quantified fairness form, so it is left out. This configuration checks  *)
(* safety only: TypeOK and ExclusiveAccess.                                *)
(***************************************************************************)
EXTENDS Integers, TLC

CONSTANTS
    \* @type: Int;
    NP

\* Apalache constant initialisation (model checked with NP = 5)
CInit == NP = 5

ASSUME NP \in Nat \ {0, 1}

VARIABLES
    \* @type: Int -> { holder: Int, clean: Bool };
    forks,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    hungry

vars == << forks, pc, hungry >>

Philosophers == 1..NP
Forks        == 1..NP

(***************************************************************************)
(* Topology: philosopher p sits between fork p (left) and fork p+1        *)
(* (right, cyclic). Fork f is shared by philosophers f-1 (cyclic) and f.  *)
(***************************************************************************)
\* @type: Int => Int;
LeftForkId(p) == p
\* @type: Int => Int;
RightForkId(p) == (p % NP) + 1
\* @type: Int => Int;
LeftPhilosopher(p) == ((p + NP - 2) % NP) + 1
\* @type: Int => Int;
RightPhilosopher(p) == (p % NP) + 1

\* @type: (Int -> { holder: Int, clean: Bool }, Int) => Bool;
HoldsBothIn(f, p) ==
    /\ f[LeftForkId(p)].holder = p
    /\ f[RightForkId(p)].holder = p

\* @type: (Int -> { holder: Int, clean: Bool }, Int) => Bool;
BothCleanIn(f, p) ==
    /\ f[LeftForkId(p)].clean
    /\ f[RightForkId(p)].clean

\* @type: (Int -> { holder: Int, clean: Bool }, Int) => Bool;
CanEatIn(f, p) == HoldsBothIn(f, p) /\ BothCleanIn(f, p)

\* @type: Int => Bool;
CanEat(p) == CanEatIn(forks, p)

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ forks \in [Forks -> [holder : Philosophers, clean : BOOLEAN]]
    /\ pc \in [Philosophers -> {"Loop", "Eat", "Think"}]
    /\ hungry \in [Philosophers -> BOOLEAN]

(***************************************************************************)
(* Initial state: every fork is dirty. Each fork goes to the lower-       *)
(* numbered of its two neighbours, so the precedence graph is acyclic.    *)
(* Fork 1 goes to philosopher 1, and fork f > 1 goes to philosopher f-1.  *)
(***************************************************************************)
Init ==
    /\ forks = [f \in Forks |->
                  [holder |-> IF f = 1 THEN 1 ELSE f - 1,
                   clean  |-> FALSE]]
    /\ pc = [p \in Philosophers |-> "Loop"]
    /\ hungry = [p \in Philosophers |-> TRUE]

(***************************************************************************)
(* Loop: if holding a dirty fork, clean it and pass it to the neighbour   *)
(* who shares it. Then go to Eat if hungry and able to eat, go to Think   *)
(* if not hungry, and otherwise keep looping.                             *)
(***************************************************************************)
\* @type: Int => Bool;
Loop(self) ==
    /\ pc[self] = "Loop"
    /\ LET lf == LeftForkId(self)
           rf == RightForkId(self)
           nf == IF forks[lf].holder = self /\ ~forks[lf].clean
                   THEN [forks EXCEPT ![lf] =
                           [holder |-> LeftPhilosopher(self), clean |-> TRUE]]
                 ELSE IF forks[rf].holder = self /\ ~forks[rf].clean
                   THEN [forks EXCEPT ![rf] =
                           [holder |-> RightPhilosopher(self), clean |-> TRUE]]
                 ELSE forks
       IN
         /\ forks' = nf
         /\ pc' = [pc EXCEPT ![self] =
                     IF hungry[self]
                       THEN IF CanEatIn(nf, self) THEN "Eat" ELSE "Loop"
                       ELSE "Think"]
    /\ UNCHANGED hungry

(***************************************************************************)
(* Eat: become satisfied and dirty both forks.                             *)
(***************************************************************************)
\* @type: Int => Bool;
Eat(self) ==
    /\ pc[self] = "Eat"
    /\ hungry' = [hungry EXCEPT ![self] = FALSE]
    /\ forks' = [forks EXCEPT
                   ![LeftForkId(self)].clean  = FALSE,
                   ![RightForkId(self)].clean = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

(***************************************************************************)
(* Think: become hungry again.                                             *)
(***************************************************************************)
\* @type: Int => Bool;
Think(self) ==
    /\ pc[self] = "Think"
    /\ hungry' = [hungry EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]
    /\ UNCHANGED forks

\* @type: Int => Bool;
Philosopher(self) == Loop(self) \/ Eat(self) \/ Think(self)

Next == \E self \in Philosophers : Philosopher(self)

(***************************************************************************)
(* Safety-only specification. The original weak fairness,                 *)
(*   \A self \in Philosophers : WF_vars(Philosopher(self)),               *)
(* is omitted because Apalache does not support it.                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Mutual exclusion: two adjacent philosophers never eat at the same      *)
(* time, so they never both use the fork between them.                    *)
(***************************************************************************)
ExclusiveAccess ==
    \A p \in Philosophers :
        pc[p] = "Eat" =>
            /\ CanEat(p)
            /\ pc[LeftPhilosopher(p)] # "Eat"
            /\ pc[RightPhilosopher(p)] # "Eat"

=============================================================================