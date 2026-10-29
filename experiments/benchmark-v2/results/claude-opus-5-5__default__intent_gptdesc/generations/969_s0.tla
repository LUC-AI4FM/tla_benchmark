------------------------------ MODULE GraphReachability ------------------------------
(***************************************************************************)
(* Directed finite-state graphs as transition systems, with an abstract    *)
(* reachability / violation-detection / counterexample-extraction tool.   *)
(*                                                                         *)
(* The specification is parametric:                                       *)
(*   Nodes     - finite set of graph nodes (may be empty)                  *)
(*   InitNodes - distinguished initial nodes                               *)
(*   Labels    - transition labels (may be empty)                          *)
(*   Delta     - labeled nondeterministic transition relation:             *)
(*               Delta[n, l] is the set of possible successors of n under  *)
(*               label l. The set may be empty.                            *)
(*   Bad       - designated "bad" nodes                                    *)
(*                                                                         *)
(* No algorithm is prescribed. The tool state evolves by any sound         *)
(* discovery step, in any order. It may terminate only once its knowledge  *)
(* is closed under successors. On termination it must publish a verdict    *)
(* and, if the verdict is unsafe, some valid counterexample path.          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, InitNodes, Labels, Delta, Bad

ASSUME GraphAssumptions ==
    /\ IsFiniteSet(Nodes)
    /\ IsFiniteSet(Labels)
    /\ InitNodes \subseteq Nodes
    /\ Bad \subseteq Nodes
    /\ Delta \in [Nodes \X Labels -> SUBSET Nodes]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Graph semantics                                                         *)
(***************************************************************************)

\* All possible successors of n, over all labels. This set may be empty
\* when n is a sink.
Succ(n) == UNION { Delta[n, l] : l \in Labels }

\* There is an edge from m to n under some label.
Edge(m, n) == \E l \in Labels : n \in Delta[m, l]

\* A finite path: a nonempty node sequence whose consecutive nodes are
\* related by some labeled transition.
IsGraphPath(p) ==
    /\ Len(p) >= 1
    /\ \A i \in 1..Len(p) : p[i] \in Nodes
    /\ \A i \in 1..(Len(p) - 1) : Edge(p[i], p[i+1])

\* A run prefix: a finite path that starts at an initial node.
IsRun(p) == IsGraphPath(p) /\ p[1] \in InitNodes

\* A counterexample: a run that ends at a bad node.
IsCounterexample(p) == IsRun(p) /\ p[Len(p)] \in Bad

\* Simple paths have length at most |Nodes|. Every reachable node is
\* therefore reachable by a path of at most this length. This bounds the
\* finite-path semantics without loss of generality.
MaxLen == Cardinality(Nodes)

BoundedSeqs == UNION { [1..k -> Nodes] : k \in 1..MaxLen }

BoundedRuns == { p \in BoundedSeqs : IsRun(p) }

Counterexamples == { p \in BoundedSeqs : IsCounterexample(p) }

\* Reference semantics: the nodes reachable from InitNodes via zero or more
\* transitions. Each such node is the endpoint of some finite run.
Reach == { n \in Nodes : \E p \in BoundedRuns : p[Len(p)] = n }

\* Equivalent least-fixpoint characterization. It is used only to state
\* the soundness and completeness obligation relative to path semantics.
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    LET T == S \cup UNION { Succ(n) : n \in S }
    IN  IF T = S THEN S ELSE ReachFrom(T)

ReachFix == ReachFrom(InitNodes)

\* The ground truth about violations.
ViolationExists == Reach \cap Bad # {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract analysis tool                                                  *)
(***************************************************************************)
VARIABLES
    reached,   \* nodes the tool has established as reachable
    done,      \* has the analysis terminated?
    verdict,   \* "pending", "safe", or "unsafe"
    cex        \* counterexample path (<<>> when none is returned)

vars == << reached, done, verdict, cex >>

Verdicts == { "pending", "safe", "unsafe" }

TypeOK ==
    /\ reached \subseteq Nodes
    /\ done \in BOOLEAN
    /\ verdict \in Verdicts
    /\ cex \in Seq(Nodes)

\* The tool's knowledge is closed under successors.
Closed == \A m \in reached : Succ(m) \subseteq reached

Init ==
    /\ reached = InitNodes
    /\ done = FALSE
    /\ verdict = "pending"
    /\ cex = << >>

\* Discover a new node that is a successor of an already-known node.
\* Any order is allowed; no exploration strategy is prescribed.
Discover ==
    /\ ~done
    /\ \E m \in reached, n \in Nodes :
          /\ Edge(m, n)
          /\ n \notin reached
          /\ reached' = reached \cup {n}
    /\ UNCHANGED << done, verdict, cex >>

\* Terminate with a "safe" verdict and no counterexample.
FinishSafe ==
    /\ ~done
    /\ Closed
    /\ reached \cap Bad = {}
    /\ done' = TRUE
    /\ verdict' = "safe"
    /\ cex' = << >>
    /\ UNCHANGED reached

\* Terminate with an "unsafe" verdict, returning some valid counterexample.
\* Any valid counterexample is acceptable.
FinishUnsafe ==
    /\ ~done
    /\ Closed
    /\ reached \cap Bad # {}
    /\ \E p \in Counterexamples : cex' = p
    /\ done' = TRUE
    /\ verdict' = "unsafe"
    /\ UNCHANGED reached

\* After termination the outputs are stable.
Terminated ==
    /\ done
    /\ UNCHANGED vars

Next == Discover \/ FinishSafe \/ FinishUnsafe \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Discover \/ FinishSafe \/ FinishUnsafe)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants (correctness obligations)                             *)
(***************************************************************************)

\* Reachability semantics: path-based and fixpoint characterizations agree.
\* This covers soundness and completeness relative to finite paths.
ReachSemanticsAgree == Reach = ReachFix

\* Soundness: everything the tool reports as reached is truly reachable.
ReachedSound == reached \subseteq Reach

\* Completeness: on termination the tool has found exactly the reachable set.
ReachedComplete == done => reached = Reach

\* Obligation (1): any returned counterexample is a valid run ending in Bad.
CounterexampleValid ==
    verdict = "unsafe" =>
        /\ IsCounterexample(cex)
        /\ cex[1] \in InitNodes
        /\ cex[Len(cex)] \in Bad
        /\ \A i \in 1..(Len(cex) - 1) : cex[i+1] \in Succ(cex[i])

\* Obligation (2): if no counterexample is returned, no bad node is reachable.
NoCexImpliesSafe ==
    (done /\ cex = << >>) => ~ViolationExists

SafeVerdictCorrect == verdict = "safe" => ~ViolationExists

\* Violation detection is exact on termination.
VerdictExact ==
    done => (/\ verdict # "pending"
             /\ (verdict = "unsafe" <=> ViolationExists))

\* A counterexample is returned exactly when the verdict is unsafe.
CexIffUnsafe == (cex # << >>) <=> (verdict = "unsafe")

\* Outputs stay unset until termination.
PendingUntilDone == ~done => (verdict = "pending" /\ cex = << >>)

\* Edge case: an empty graph or empty initial set yields an empty
\* reachable set and a safe verdict.
EmptyCase ==
    (InitNodes = {}) => (Reach = {} /\ (done => verdict = "safe"))

Invariants ==
    /\ TypeOK
    /\ ReachSemanticsAgree
    /\ ReachedSound
    /\ ReachedComplete
    /\ CounterexampleValid
    /\ NoCexImpliesSafe
    /\ SafeVerdictCorrect
    /\ VerdictExact
    /\ CexIffUnsafe
    /\ PendingUntilDone
    /\ EmptyCase

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* The analysis always terminates (the graph is finite).
Termination == <>done

\* Once terminated, the result is permanent.
StableResult == [](done => [](done /\ verdict' = verdict /\ cex' = cex))

\* Eventually the correct verdict is produced.
EventuallyCorrect ==
    <>(done /\ (verdict = "unsafe" <=> ViolationExists))

\* Every reachable node is eventually discovered.
EventuallyAllReached == \A n \in Reach : <>(n \in reached)

\* A reachable violation is eventually reported with a counterexample.
ViolationReported == ViolationExists => <>(verdict = "unsafe" /\ cex # << >>)

THEOREM Spec => []Invariants
THEOREM Spec => Termination /\ EventuallyCorrect /\ EventuallyAllReached
=============================================================================