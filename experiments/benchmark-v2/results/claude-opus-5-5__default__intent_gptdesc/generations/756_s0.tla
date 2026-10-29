-------------------------------- MODULE JugPuzzle --------------------------------
(***************************************************************************)
(* Generalized water-jug measuring puzzle.                                 *)
(*                                                                         *)
(* A finite set of jugs, each with a fixed nonnegative integer capacity.   *)
(* Operations: fill a jug from an infinite source, empty a jug into an     *)
(* infinite sink, or pour one jug into another until the source is empty   *)
(* or the destination is full.                                             *)
(*                                                                         *)
(* Reachability: is there a state in which some jug holds exactly Goal?    *)
(*                                                                         *)
(* WITNESS GENERATION: check the invariant  NotSolved  with TLC.           *)
(* If Goal is reachable within MaxSteps, TLC reports a violation and the   *)
(* error trace is a witness sequence of operations. The trace records      *)
(* each operation in lastOp. TLC uses BFS, so this trace is a shortest     *)
(* witness.                                                                *)
(*                                                                         *)
(* Example concrete instance (Die Hard 3), as a TLC .cfg file:             *)
(*   CONSTANTS                                                             *)
(*     Jugs = {j3, j5}          \* model values                            *)
(*     Capacity <- CapInst      \* CapInst == (j3 :> 3) @@ (j5 :> 5)       *)
(*     InitAmount <- InitInst   \* InitInst == (j3 :> 0) @@ (j5 :> 0)      *)
(*     Goal = 4                                                            *)
(*     MaxSteps = 10                                                       *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANTS TypeOK CapacityBounds AmountsMultipleOfGcd NoSpurious      *)
(*              SolvedSound                                                *)
(*   PROPERTIES Conservation TotalChangesOnlyByFillEmpty Termination       *)
(*              StepsMonotone                                              *)
(*   \* Add INVARIANT NotSolved to obtain a witness trace.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Jugs,        \* finite, nonempty set of jugs
    Capacity,    \* Capacity[j] \in Nat : capacity of jug j
    InitAmount,  \* InitAmount[j] : initial contents (all 0 for the classic puzzle)
    Goal,        \* target quantity
    MaxSteps     \* bound on the number of operations (bounded-step reachability)

ASSUME JugsAssump      == Jugs # {} /\ IsFiniteSet(Jugs)
ASSUME CapacityAssump  == Capacity \in [Jugs -> Nat]
ASSUME InitAssump      == /\ InitAmount \in [Jugs -> Nat]
                          /\ \A j \in Jugs : InitAmount[j] <= Capacity[j]
ASSUME GoalAssump      == Goal \in Nat
ASSUME MaxStepsAssump  == MaxSteps \in Nat

VARIABLES
    contents,   \* contents[j] : current amount of water in jug j
    steps,      \* number of operations performed so far
    lastOp      \* the most recent operation (for readable witness traces)

vars == <<contents, steps, lastOp>>

-----------------------------------------------------------------------------
(* Helper operators *)

Min(a, b) == IF a <= b THEN a ELSE b

SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN  f[x] + SumF(f, S \ {x})

Total(f) == SumF(f, Jugs)

MaxCap == SetMax({Capacity[j] : j \in Jugs})

\* Greatest common divisor of all capacities (1 if all capacities are 0).
CommonDivisors == {d \in 1..MaxCap : \A j \in Jugs : Capacity[j] % d = 0}
G == IF CommonDivisors = {} THEN 1 ELSE SetMax(CommonDivisors)

Ops == {"init", "fill", "empty", "pour"}

Solved == \E j \in Jugs : contents[j] = Goal

Done == Solved \/ steps >= MaxSteps

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ contents = InitAmount
    /\ steps = 0
    /\ lastOp = [op |-> "init", src |-> {}, dst |-> {}]

-----------------------------------------------------------------------------
(* Actions. They are enabled only while the search is not finished. *)

Fill(j) ==
    /\ ~Done
    /\ contents' = [contents EXCEPT ![j] = Capacity[j]]
    /\ steps' = steps + 1
    /\ lastOp' = [op |-> "fill", src |-> {}, dst |-> {j}]

Empty(j) ==
    /\ ~Done
    /\ contents' = [contents EXCEPT ![j] = 0]
    /\ steps' = steps + 1
    /\ lastOp' = [op |-> "empty", src |-> {j}, dst |-> {}]

Pour(j, k) ==
    /\ ~Done
    /\ j # k
    /\ LET amt == Min(contents[j], Capacity[k] - contents[k])
       IN  contents' = [contents EXCEPT ![j] = @ - amt, ![k] = @ + amt]
    /\ steps' = steps + 1
    /\ lastOp' = [op |-> "pour", src |-> {j}, dst |-> {k}]

\* Terminal stuttering: the search is over (solved or step bound reached).
Halt ==
    /\ Done
    /\ UNCHANGED vars

Next ==
    \/ \E j \in Jugs : Fill(j)
    \/ \E j \in Jugs : Empty(j)
    \/ \E j, k \in Jugs : Pour(j, k)
    \/ Halt

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ contents \in [Jugs -> Nat]
    /\ steps \in 0..MaxSteps
    /\ lastOp.op \in Ops
    /\ lastOp.src \subseteq Jugs
    /\ lastOp.dst \subseteq Jugs

\* Contents never exceed capacity and are never negative.
CapacityBounds == \A j \in Jugs : 0 <= contents[j] /\ contents[j] <= Capacity[j]

\* Number-theoretic invariant: if all initial amounts are multiples of
\* gcd(capacities), every reachable amount is too.
AmountsMultipleOfGcd ==
    (\A j \in Jugs : InitAmount[j] % G = 0) => (\A j \in Jugs : contents[j] % G = 0)

\* Rules out spurious solutions: if Goal is provably impossible, then Goal is
\* never reported as reached. This holds when Goal exceeds every capacity, or
\* when Goal is not a multiple of the gcd and all initial amounts are multiples.
Impossible ==
    \/ Goal > MaxCap
    \/ /\ Goal % G # 0
       /\ \A j \in Jugs : InitAmount[j] % G = 0

NoSpurious == Impossible => ~Solved

\* Any reported solution is genuine.
SolvedSound == Solved => \E j \in Jugs : contents[j] = Goal /\ Goal <= Capacity[j]

\* Witness invariant. A TLC violation of this invariant is the witness trace.
NotSolved == ~Solved

-----------------------------------------------------------------------------
(* Action (temporal) safety properties *)

\* Pouring conserves the total amount of water.
Conservation ==
    [][(lastOp'.op = "pour" /\ steps' = steps + 1) => Total(contents') = Total(contents)]_vars

\* The total changes only through fill or empty operations.
TotalChangesOnlyByFillEmpty ==
    [][Total(contents') # Total(contents) => lastOp'.op \in {"fill", "empty"}]_vars

StepsMonotone == [][steps' >= steps]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: under weak fairness, every behavior eventually finds the goal
\* or exhausts the step bound.
Termination == <>Done

\* Once the search is finished, it stays finished.
DoneStable == [](Done => []Done)

\* Liveness of reachability ("some finite sequence of operations reaches the
\* goal") is existential. It is witnessed by a violation of NotSolved, which
\* yields a finite trace of at most MaxSteps operations ending in Solved.
\* The universal version below holds only for instances where every fair
\* path solves the puzzle. It is provided for exploration.
EventuallySolved == <>Solved

=============================================================================