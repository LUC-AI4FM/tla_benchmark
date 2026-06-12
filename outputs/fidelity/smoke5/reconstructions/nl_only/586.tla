---- MODULE TraceValidationWrapper ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    TraceLogFile,
    ReadFile(_),
    JsonDeserialize(_),
    EventMatches(_, _, _),
    IsBackfillStep(_, _)

VARIABLES l

MNR == INSTANCE MultiNodeReads

vars == MNR!vars

Trace == JsonDeserialize(ReadFile(TraceLogFile))

TLCEnvironmentAssumption ==
    Assert(
        /\ TLCGet("mode") = "bfs"
        /\ TLCGet("workers") = 1,
        "This trace-validation wrapper assumes TLC breadth-first execution with one worker."
    )

Init ==
    /\ TLCEnvironmentAssumption
    /\ l = 1
    /\ MNR!Init

LoggedStep ==
    /\ l \in 1..Len(Trace)
    /\ MNR!Next
    /\ EventMatches(Trace[l], vars, vars')
    /\ l' = l + 1

BackfillStep ==
    /\ l \in 1..(Len(Trace) + 1)
    /\ MNR!Next
    /\ IsBackfillStep(vars, vars')
    /\ l' = l

Next ==
    LoggedStep \/ BackfillStep

Spec ==
    Init /\ [][Next]_<<l, vars>>

TraceFullyMatched ==
    <>(l = Len(Trace) + 1)

TraceEventuallyStaysMatched ==
    <>[](l = Len(Trace) + 1)

TraceMatchWasNonTrivial ==
    <>(l > 1)

====