------------------------------- MODULE NBAC ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Procs \* The set of processes
    Vars  \* The set of variables that can be voted on

VARIABLES 
    vote,      \* vote[v][p] is the vote (YES/NO) of process p for variable v
    msg,       \* msg[v][p] is a sequence of messages received by process p for variable v
    failureDet,\* failureDet[p] is the set of processes that process p believes have crashed
    committed  \* committed[v] indicates whether variable v has been committed (TRUE/FALSE)

Init == 
    /\ \/ committed = [v \in Vars |-> FALSE]
    /\ /\ vote = [v \in Vars, p \in Procs |-> UNCHANGED]
       /\ msg = [v \in Vars, p \in Procs |-> <<>>]
       /\ failureDet = [p \in Procs |-> {}]

ProcessStep(v, p) ==
    LET 
        localVotes == {vote[v][q] : q \notin failureDet[p]}
        localYesCount == Cardinality({x \in localVotes : x = "YES"})
        localNoCount == Cardinality({x \in localVotes : x = "NO"})
    IN
    \/ /\ msg'[v][p] = Append(msg[v][p], <<>>)
       /\ committed'[v] = IF localYesCount > 0 /\ localNoCount = 0 THEN TRUE ELSE committed[v]
       /\ failureDet' = failureDet
       /\ vote' = vote
    \/ /\ \E m \in msg[v][p] : 
            (m[1] \in Vars /\ m[2] \in Procs /\ m[3] \in {"YES", "NO"})
           /\ msg'[v][p] = [msg[v][p] EXCEPT ![Len(msg[v][p])] = <<>>]
           /\ IF m[1] = v THEN vote'[m[1]][m[2]] = m[3] ELSE vote' = vote
           /\ failureDet'[p] = failureDet[p] \cup {m[2]}
           /\ committed'[v] = committed[v]

Next ==
    \/ /\ Init
       /\ committed' = committed
       /\ msg' = msg
       /\ failureDet' = failureDet
       /\ vote' = vote
    \/ /\ \E v \in Vars, p \in Procs :
            ProcessStep(v, p)
           /\ /\ committed' = [v \in Vars |-> IF v = v THEN committed[v] ELSE committed'[v]]
              /\ msg' = [v \in Vars, p \in Procs |-> IF v = v /\ p = p THEN msg[v][p] ELSE msg'[v][p]]
              /\ failureDet' = [p \in Procs |-> IF p = p THEN failureDet[p] ELSE failureDet'[p]]
              /\ vote' = [v \in Vars, p \in Procs |-> IF v = v /\ p = p THEN vote[v][p] ELSE vote'[v][p]]

Spec ==
    WF_next(Next) /\ []Init /\ <>([]TypeOK)

TypeOK ==
    /\ committed \in [Vars -> BOOLEAN]
    /\ vote \in [Vars -> [Procs -> {"YES", "NO", UNCHANGED}]]
    /\ msg \in [Vars -> [Procs -> Seq({"YES", "NO"})]]
    /\ failureDet \in [Procs -> SUBSET Procs]

Validity ==
    []<>(\A v \in Vars : committed[v] => (\A p \in Procs : vote[v][p] = "YES"))

SpecWithProperties ==
    Spec /\ Validity

=============================================================================