---------------------------- MODULE TimestampAllocator ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS k1, k2, RM

\* Upper bound: no issued timestamp may be >= Limit
Limit == 4

\* Definition override for RM: the two distinct label values
const_1571478437097222000 == {k1, k2}

VARIABLES
    maxTs,      \* current highest issued timestamp (0 = none issued yet)
    req,        \* req[r] = TRUE iff label r has an outstanding request
    tsOf,       \* tsOf[r] = last timestamp assigned to label r (0 = none)
    issued,     \* set of all timestamps issued so far
    hist,       \* sequence of timestamps in issuance order
    resolved    \* highest timestamp up to which all issued timestamps are resolved

vars == <<maxTs, req, tsOf, issued, hist, resolved>>

\* State constraint that keeps the model finite
constr_1571478437097223000 ==
    /\ maxTs < Limit
    /\ Len(hist) < Limit

RTTypeOK ==
    /\ maxTs \in 0..(Limit - 1)
    /\ req \in [RM -> BOOLEAN]
    /\ tsOf \in [RM -> 0..(Limit - 1)]
    /\ issued \subseteq 1..(Limit - 1)
    /\ hist \in Seq(1..(Limit - 1))
    /\ resolved \in 0..(Limit - 1)

Init ==
    /\ maxTs = 0
    /\ req = [r \in RM |-> FALSE]
    /\ tsOf = [r \in RM |-> 0]
    /\ issued = {}
    /\ hist = << >>
    /\ resolved = 0

\* A label presents a new timestamp request (arrivals interleave nondeterministically)
Request(r) ==
    /\ ~req[r]
    /\ req' = [req EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<maxTs, tsOf, issued, hist, resolved>>

\* Allocator serves a pending request with a fresh, strictly larger timestamp
Assign(r) ==
    /\ req[r]
    /\ maxTs + 1 < Limit
    /\ maxTs' = maxTs + 1
    /\ tsOf' = [tsOf EXCEPT ![r] = maxTs + 1]
    /\ issued' = issued \cup {maxTs + 1}
    /\ hist' = Append(hist, maxTs + 1)
    /\ req' = [req EXCEPT ![r] = FALSE]
    /\ UNCHANGED resolved

\* Advance the resolved watermark to the highest issued timestamp
Resolve ==
    /\ resolved < maxTs
    /\ resolved' = maxTs
    /\ UNCHANGED <<maxTs, req, tsOf, issued, hist>>

\* Once the bound is exhausted and everything resolved, the system idles
Done ==
    /\ maxTs + 1 >= Limit
    /\ resolved = maxTs
    /\ UNCHANGED vars

Next ==
    \/ \E r \in RM : Request(r)
    \/ \E r \in RM : Assign(r)
    \/ Resolve
    \/ Done

RTSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A r \in RM : WF_vars(Assign(r))
    /\ WF_vars(Resolve)

-----------------------------------------------------------------------------------
\* Safety: uniqueness, strict monotonicity, and bound enforcement
CommitConsistency ==
    /\ \A i, j \in 1..Len(hist) : i < j => hist[i] < hist[j]
    /\ Len(hist) = Cardinality(issued)
    /\ \A i \in 1..Len(hist) : hist[i] \in issued
    /\ (Len(hist) > 0) => hist[Len(hist)] = maxTs
    /\ (Len(hist) = 0) => maxTs = 0
    /\ \A t \in issued : t < Limit /\ t <= maxTs
    /\ \A r1, r2 \in RM :
          (r1 # r2 /\ tsOf[r1] # 0) => tsOf[r1] # tsOf[r2]
    /\ \A r \in RM : tsOf[r] # 0 => tsOf[r] \in issued

\* The resolved watermark never exceeds what has been issued
ResolvedConsistency ==
    /\ resolved <= maxTs
    /\ resolved < Limit
    /\ \A t \in issued : t <= resolved \/ t > resolved

\* Liveness: every issued timestamp is eventually resolved, and pending
\* requests are served whenever the bound still allows issuance
ResolveLiveness ==
    /\ \A t \in 1..(Limit - 1) : (t \in issued) ~> (resolved >= t)
    /\ \A r \in RM : (req[r] /\ maxTs + 1 < Limit) ~> (~req[r] \/ maxTs + 1 >= Limit)

===================================================================================