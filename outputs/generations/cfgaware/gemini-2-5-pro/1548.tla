---- MODULE OneStepConsensus ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, F, T

\* Assumptions on parameters for the algorithm to be correct.
ASSUME N > 3*F /\ T > (N+F)/2

Procs == 1..N
Value == {0, 1}

VARIABLES
    \* The program counter for each process.
    pc,
    \* The set of faulty processes.
    faulty,
    \* The initial value proposed by each process.
    proposal,
    \* The value sent by each process. "undefined" if not sent yet.
    sent_from,
    \* received_by[p][q] is the value p received from q.
    received_by,
    \* The decision value for each process. "undefined" if not decided.
    decision

vars == <<pc, faulty, proposal, sent_from, received_by, decision>>

\* Initial state predicates for all-0 and all-1 proposals.
Init(val_func) ==
    /\ faulty = {}
    /\ pc = [p \in Procs |-> "propose"]
    /\ proposal = val_func
    /\ sent_from = [p \in Procs |-> "undefined"]
    /\ received_by = [p \in Procs |-> [q \in Procs |-> "undefined"]]
    /\ decision = [p \in Procs |-> "undefined"]

Init0 == Init([p \in Procs |-> 0])
Init1 == Init([p \in Procs |-> 1])

Init == Init0 \/ Init1

\* A correct process p sends its proposal value.
Propose(p) ==
    /\ p \in Procs \setminus faulty
    /\ pc[p] = "propose"
    /\ sent_from' = [sent_from EXCEPT ![p] = proposal[p]]
    /\ pc' = [pc EXCEPT ![p] = "receive"]
    /\ UNCHANGED <<faulty, proposal, received_by, decision>>

\* A correct process p receives a message from process q.
\* If q is faulty, it can send any value. Otherwise, it sends its true value.
Receive(p, q) ==
    /\ p \in Procs \setminus faulty
    /\ pc[p] = "receive"
    /\ sent_from[q] # "undefined"
    /\ received_by[p][q] = "undefined"
    /\ LET v_sent = sent_from[q]
       v_options = IF q \in faulty THEN Value ELSE {v_sent}
       IN \E v \in v_options :
            received_by' = [received_by EXCEPT ![p][q] = v]
    /\ UNCHANGED <<pc, faulty, proposal, sent_from, decision>>

\* A correct process p decides after receiving N-F messages.
\* It decides v if it received at least T messages for v, otherwise defaults to 0.
Decide(p) ==
    /\ p \in Procs \setminus faulty
    /\ pc[p] = "receive"
    /\ Cardinality({q \in Procs : received_by[p][q] # "undefined"}) >= N - F
    /\ LET count(v) == Cardinality({q \in Procs : received_by[p][q] = v})
       decision_val ==
           IF \E v \in Value : count(v) >= T
           THEN CHOOSE v \in Value : count(v) >= T
           ELSE 0 \* Default decision value
    /\ decision' = [decision EXCEPT ![p] = decision_val]
    /\ pc' = [pc EXCEPT ![p] = "decide"]
    /\ UNCHANGED <<faulty, proposal, sent_from, received_by>>

\* A correct process p becomes faulty, up to a maximum of F.
BecomeFaulty(p) ==
    /\ p \in Procs \setminus faulty
    /\ Cardinality(faulty) < F
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED <<pc, proposal, sent_from, received_by, decision>>

Next ==
    \/ \E p \in Procs : Propose(p)
    \/ \E p, q \in Procs : Receive(p, q)
    \/ \E p \in Procs : Decide(p)
    \/ \E p \in Procs : BecomeFaulty(p)

\* The main specification with weak fairness on the next-state relation.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Type invariant for model checking.
TypeOK ==
    /\ faulty \subseteq Procs
    /\ Cardinality(faulty) <= F
    /\ pc \in [Procs -> {"propose", "receive", "decide"}]
    /\ proposal \in [Procs -> Value]
    /\ sent_from \in [Procs -> Value \cup {"undefined"}]
    /\ received_by \in [Procs -> [Procs -> Value \cup {"undefined"}]]
    /\ decision \in [Procs -> Value \cup {"undefined"}]

\* --- Properties ---

Correct == Procs \setminus faulty

\* Termination: All correct processes eventually decide.
Termination == \A p \in Correct : <>(pc[p] = "decide")

\* Agreement: All correct processes that decide, decide the same value.
Agreement ==
    \A p, q \in Correct :
        []( (pc[p] = "decide" /\ pc[q] = "decide") => decision[p] = decision[q] )

\* Validity: If all correct processes propose v, they must decide v.
Validity(v_prop) ==
    (\A p \in Correct : proposal[p] = v_prop) =>
        (\A q \in Correct : pc[q] = "decide" => decision[q] = v_prop)

\* Liveness property for the all-0 initial case.
OneStep0_Ltl ==
    (\A p \in Procs : proposal[p] = 0) ~> (Termination /\ Agreement /\ []Validity(0))

\* Liveness property for the all-1 initial case.
OneStep1_Ltl ==
    (\A p \in Procs : proposal[p] = 1) ~> (Termination /\ Agreement /\ []Validity(1))

\* A reachability property: is it possible for all correct processes to decide 1?
AllDecideOne == <>(\A p \in Correct : decision[p] = 1)

=============================================================================