------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProc, MaxTicket

VARIABLES state, choosing, ticket, nextNum

(* --algorithm bakery
variables 
  state = [p \in 1..NumProc |-> "idle"],
  choosing = [p \in 1..NumProc |-> FALSE],
  ticket = [p \in 1..NumProc |-> 0],
  nextNum = 1;

process with p \in 1..NumProc
begin
Entry:
    while TRUE do
        choose: await \A q \in 1..NumProc \ {p} : ~choosing[q];
        choosing[p] := TRUE;
        findNextNum:
            n \in 1..MaxTicket \ {ticket[q] : q \in 1..NumProc};
            ticket[p] := n;
        exitChoosing: choosing[p] := FALSE;

        requestCS:
            await \A q \in 1..NumProc \ {p} :
                ~choosing[q] \/ (ticket[q] = 0) \/ (<<ticket[q], q>> > <<ticket[p], p>>);
        state[p] := "critical section";
        inCS: skip;
        state[p] := "idle";
end process;

 fairness assumptions
 WF_{!!} \A p \in 1..NumProc : pc[p] = "choose"
 WF_{!!} \A p \in 1..NumProc : pc[p] = "findNextNum"
 WF_{!!} \A p \in 1..NumProc : pc[p] = "exitChoosing"
 WF_{!!} \A p \in 1..NumProc : pc[p] = "requestCS"
*)

Init == /\ state \in [1..NumProc -> {"idle", "critical section"}]
        /\ choosing \in [1..NumProc -> BOOLEAN]
        /\ ticket \in [1..NumProc -> 0..MaxTicket]
        /\ nextNum \in 1..MaxTicket

Next ==
    \/ /\ \E p \in 1..NumProc : 
            /\ state[p] = "idle"
            /\ ~(\E q \in 1..NumProc \ {p} : choosing[q])
            /\ choosing' = [choosing EXCEPT ![p] = TRUE]
            /\ UNCHANGED <<state, ticket, nextNum>>
    \/ /\ \E p \in 1..NumProc :
            /\ state[p] = "idle"
            /\ choosing[p]
            /\ \E n \in 1..MaxTicket \ {ticket[q] : q \in 1..NumProc} :
                /\ ticket' = [ticket EXCEPT ![p] = n]
                /\ UNCHANGED <<state, choosing, nextNum>>
    \/ /\ \E p \in 1..NumProc :
            /\ state[p] = "idle"
            /\ choosing[p]
            /\ ticket[p] \in 1..MaxTicket
            /\ choosing' = [choosing EXCEPT ![p] = FALSE]
            /\ UNCHANGED <<state, ticket, nextNum>>
    \/ /\ \E p \in 1..NumProc :
            /\ state[p] = "idle"
            /\ ~(\E q \in 1..NumProc \ {p} : choosing[q])
            /\ ~(\E q \in 1..NumProc \ {p} : ticket[q] # 0 \/ <<ticket[q], q>> > <<ticket[p], p>>)
            /\ state' = [state EXCEPT ![p] = "critical section"]
            /\ UNCHANGED <<choosing, ticket, nextNum>>
    \/ /\ \E p \in 1..NumProc :
            /\ state[p] = "critical section"
            /\ state' = [state EXCEPT ![p] = "idle"]
            /\ UNCHANGED <<choosing, ticket, nextNum>>

Spec ==
    /\ Init
    /\ [][Next]_<<state, choosing, ticket, nextNum>>
    /\ WF_<<\A p \in 1..NumProc : pc[p] = "choose">>
    /\ WF_<<\A p \in 1..NumProc : pc[p] = "findNextNum">>
    /\ WF_<<\A p \in 1..NumProc : pc[p] = "exitChoosing">>
    /\ WF_<<\A p \in 1..NumProc : pc[p] = "requestCS">>

MutualExclusion == 
    \A p, q \in 1..NumProc :
        \/ state[p] # "critical section"
        \/ state[q] # "critical section"
        \/ p = q

MaximumTicket ==
    \A t \in DOMAIN ticket : ticket[t] \leq MaxTicket

=============================================================================