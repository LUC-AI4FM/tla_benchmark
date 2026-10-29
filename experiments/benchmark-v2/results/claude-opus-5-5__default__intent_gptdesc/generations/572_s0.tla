---------------------------- MODULE ReplicatedAppendOnlyLog ----------------------------
(***************************************************************************)
(* A replicated append-only log maintained by a finite set of servers.     *)
(* Each server holds a ledger: a finite sequence of ordered (non-          *)
(* decreasing) terms that begins with MinTerm. The only permitted atomic   *)
(* effects on a server's log are:                                          *)
(*   - Copy:   a server copies part or all of the suffix of a strictly     *)
(*             longer log held by another server.                          *)
(*   - Extend: a server holding a longest log appends one or more new      *)
(*             entries.                                                    *)
(* No action removes, reorders or alters existing entries. Any two logs    *)
(* are always prefix-comparable, so there is a single branch.              *)
(* The spec does not model leader election or message passing.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Server,     \* finite set of servers
    Term,       \* ordered domain of term values (a subset of Nat)
    MinTerm,    \* minimum starting term, contained in every initial log
    MaxLen      \* bound on log length, used to keep the model finite

ASSUME ServerAssm  == IsFiniteSet(Server) /\ Server # {}
ASSUME TermAssm    == Term \subseteq Nat /\ IsFiniteSet(Term)
ASSUME MinTermAssm == MinTerm \in Term /\ \A x \in Term : MinTerm <= x
ASSUME MaxLenAssm  == MaxLen \in Nat /\ MaxLen >= 1

VARIABLES log   \* log[s] is the ledger held by server s

vars == <<log>>

-----------------------------------------------------------------------------
(* Helper operators *)

Last(l) == l[Len(l)]

\* a is a prefix of b
IsPrefix(a, b) ==
    /\ Len(a) <= Len(b)
    /\ SubSeq(b, 1, Len(a)) = a

\* a is a strict prefix of b
IsStrictPrefix(a, b) == IsPrefix(a, b) /\ Len(a) < Len(b)

\* a and b are prefix-comparable
Comparable(a, b) == IsPrefix(a, b) \/ IsPrefix(b, a)

\* terms in a sequence are in non-decreasing order
Ordered(l) == \A i \in 1..(Len(l) - 1) : l[i] <= l[i + 1]

\* s holds a longest log
IsLongest(s) == \A t \in Server : Len(log[t]) <= Len(log[s])

\* every server other than s keeps its log
OthersUnchanged(s) ==
    /\ DOMAIN log' = Server
    /\ \A t \in Server \ {s} : log'[t] = log[t]

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ log \in [Server -> Seq(Term)]
    /\ \A s \in Server :
         /\ Len(log[s]) >= 1
         /\ Len(log[s]) <= MaxLen
         /\ log[s][1] = MinTerm
         /\ Ordered(log[s])

-----------------------------------------------------------------------------
(* Initial state: every server holds the identical minimal ledger. *)

Init == log = [s \in Server |-> <<MinTerm>>]

-----------------------------------------------------------------------------
(* Concrete actions *)

(* Server s copies the next k - Len(log[s]) entries of t's strictly longer
   log. It may copy part or all of the missing suffix. *)
Copy(s, t) ==
    /\ s # t
    /\ Len(log[s]) < Len(log[t])
    /\ IsPrefix(log[s], log[t])
    /\ \E k \in (Len(log[s]) + 1)..Len(log[t]) :
         log' = [log EXCEPT ![s] = SubSeq(log[t], 1, k)]

(* A server with a longest log appends n >= 1 new entries. The new terms
   are non-decreasing and no smaller than its current last term. The
   number of entries and their terms are nondeterministic. *)
Extend(s) ==
    /\ IsLongest(s)
    /\ \E n \in 1..(MaxLen - Len(log[s])) :
         \E ext \in [1..n -> Term] :
            /\ ext[1] >= Last(log[s])
            /\ Ordered(ext)
            /\ log' = [log EXCEPT ![s] = log[s] \o ext]

Next ==
    \/ \E s, t \in Server : Copy(s, t)
    \/ \E s \in Server : Extend(s)

-----------------------------------------------------------------------------
(* Fairness and specification *)

Fairness ==
    /\ WF_vars(\E s \in Server : Extend(s))               \* leaders extend
    /\ \A s, t \in Server : WF_vars(Copy(s, t))           \* followers catch up

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Axiomatized abstract actions. These are described only by their effect
   on the logs, not by how the effect is achieved. *)

(* s's log grows strictly and stays a prefix of some other server's log. *)
CopyAbs(s) ==
    /\ \E t \in Server :
         /\ IsStrictPrefix(log[s], log'[s])
         /\ IsPrefix(log'[s], log[t])
    /\ OthersUnchanged(s)

(* A longest log grows strictly, stays well-formed and stays in bounds. *)
ExtendAbs(s) ==
    /\ IsLongest(s)
    /\ IsStrictPrefix(log[s], log'[s])
    /\ log'[s] \in Seq(Term)
    /\ Len(log'[s]) <= MaxLen
    /\ Ordered(log'[s])
    /\ OthersUnchanged(s)

AbsNext == \E s \in Server : CopyAbs(s) \/ ExtendAbs(s)

AbsSpec == Init /\ [][AbsNext]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

\* No-divergence: any two logs are prefix-comparable (a single branch).
NoDivergence == \A s, t \in Server : Comparable(log[s], log[t])

\* Every log starts with the minimum term.
StartsWithMinTerm == \A s \in Server : log[s][1] = MinTerm

\* Combined state invariant.
Inv == TypeOK /\ NoDivergence /\ StartsWithMinTerm

\* Append-only: no server ever loses, reorders or modifies past entries.
AppendOnly == [][\A s \in Server : IsPrefix(log[s], log'[s])]_vars

\* Observational equivalence of each concrete action with its abstract
\* counterpart, checked on every step.
CopyEquivalence ==
    [][\A s \in Server : (\E t \in Server : Copy(s, t)) <=> CopyAbs(s)]_vars

ExtendEquivalence ==
    [][\A s \in Server : Extend(s) <=> ExtendAbs(s)]_vars

NextEquivalence == [][Next <=> AbsNext]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Followers catch up: any length reached by some log is reached by all.
CatchUp ==
    \A s, t \in Server : \A k \in 1..MaxLen :
        (Len(log[t]) >= k) ~> (Len(log[s]) >= k)

\* Leaders keep extending: the longest log eventually reaches the bound.
Progress == <>(\E s \in Server : Len(log[s]) = MaxLen)

\* Eventually all servers agree on one full-length log forever.
Convergence ==
    <>[](\A s, t \in Server : log[s] = log[t] /\ Len(log[s]) = MaxLen)

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []Inv
THEOREM Spec => AppendOnly
THEOREM Spec => CopyEquivalence /\ ExtendEquivalence /\ NextEquivalence
THEOREM Spec => AbsSpec
THEOREM AbsSpec => []NoDivergence
THEOREM Spec => CatchUp /\ Progress /\ Convergence

=============================================================================