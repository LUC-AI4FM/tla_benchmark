---- MODULE BakeryAlgorithm ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumProcesses, MaxTicketValue

VARIABLES state, ticket, choosing

(* --algorithm bakery
variables state = [p \in 1..NumProcesses |-> "not_in_CS"],
          ticket = [p \in 1..NumProcesses |-> 0],
          choosing = [p \in 1..NumProcesses |-> FALSE];
process p \in 1..NumProcesses
begin
    while TRUE do
        choosing[p] := TRUE;
        ticket[p] := (CHOOSE t \in {m \in 1..MaxTicketValue : m > Max({ticket[q]: q \in 1..NumProcesses})});
        choosing[p] := FALSE;
        with j \in 1..NumProcesses do
            await \A k \in 1..NumProcesses: \/ ~choosing[k]
                                              \/ /\ ticket[k] = 0
                                                 \/ (/\ ticket[k] > ticket[j]
                                                    \/ /\ ticket[k] = ticket[j]
                                                       \/ p < j);
        state[p] := "in_CS";
        assert \A q \in 1..NumProcesses \ {p}: state[q] # "in_CS";
        state[p] := "not_in_CS";
    end while;
end process
*)
Init == /\ state = [p \in 1..NumProcesses |-> "not_in_CS"]
        /\ ticket = [p \in 1..NumProcesses |-> 0]
        /\ choosing = [p \in 1..NumProcesses |-> FALSE]

Next ==
    \E p \in 1..NumProcesses: \/ (choosing[p] = FALSE
                                   /\ \A q \in 1..NumProcesses \ {p}: ticket[q] <= ticket[p])
                                /\ (state[p] = "not_in_CS"
                                    /\ \/ choosing' = [choosing EXCEPT ![p] = TRUE]
                                       \/ (\E t \in 1..MaxTicketValue:
                                           (ticket' = [ticket EXCEPT ![p] = t]
                                            /\ choosing' = [choosing EXCEPT ![p] = FALSE])
                                          )
                                   )
                                \/ (choosing[p] = TRUE
                                    /\ choosing' = [choosing EXCEPT ![p] = FALSE])
                                \/ (/\ state[p] = "not_in_CS"
                                    /\ \A q \in 1..NumProcesses:
                                        ~choosing[q]
                                        \/ ticket[q] = 0
                                        \/ (ticket[q] > ticket[p]
                                            \/ (ticket[q] = ticket[p]
                                                \/ p < q))
                                    /\ state' = [state EXCEPT ![p] = "in_CS"])
                                \/ (/\ state[p] = "in_CS"
                                    /\ \A q \in 1..NumProcesses \ {p}: state[q] # "in_CS"
                                    /\ state' = [state EXCEPT ![p] = "not_in_CS"])

Spec == Init /\ [][Next]_<<choosing, ticket, state>>

WFState == WF_next(variables <<choosing, ticket, state>>, Next)

MutualExclusion == \A p, q \in 1..NumProcesses: p # q => [](state[p] = "in_CS" => state[q] # "in_CS")

TypeInvariant ==
    /\ state \in [1..NumProcesses -> {"not_in_CS", "in_CS"}]
    /\ ticket \in [1..NumProcesses -> 0..MaxTicketValue]
    /\ choosing \in [1..NumProcesses -> BOOLEAN]

Spec == Spec /\ WFState /\ MutualExclusion /\ TypeInvariant
====