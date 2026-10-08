------------------------------- MODULE BakeryAlgorithm -------------------------------

CONSTANTS NumProcs, MaxNum

VARIABLES ticket, choosing

(*--algorithm bakery
variables 
    ticket = [p \in 1..NumProcs -> 0],
    choosing = [p \in 1..NumProcs -> FALSE];

process (Proc \in 1..NumProcs)
begin
ChooseTicket:
    choosing[Proc] := TRUE;
    ticket[Proc] := 1 + Max({ticket[p] : p \in 1..NumProcs});
    choosing[Proc] := FALSE;

WaitForTurn:
    await \A q \in 1..NumProcs: \/ ~choosing[q]
                                 \/ /\ ticket[q] = 0
                                    \/ ticket[q] > ticket[Proc]
                                    \/ /\ ticket[q] = ticket[Proc]
                                       \/ Proc < q;
    
CriticalSection:
    skip;

ReleaseTicket:
    ticket[Proc] := 0;
end process;
end algorithm*)

Invariant == 
    \A p, q \in 1..NumProcs: \/ ticket[p] = 0
                              \/ ticket[q] = 0
                              \/ ticket[p] > ticket[q]
                              \/ /\ ticket[p] = ticket[q]
                                 \/ p < q
/\ \A p \in 1..NumProcs: ticket[p] \leq MaxNum

MutualExclusion ==
    \A p, q \in 1..NumProcs: \/ ticket[p] = 0
                              \/ ticket[q] = 0
                              \/ ticket[p] > ticket[q]
                              \/ /\ ticket[p] = ticket[q]
                                 \/ p < q

SafetyOfTicketManagement ==
    \A p \in 1..NumProcs: ticket[p] \leq MaxNum

NoDeadlock ==
    \E p \in 1..NumProcs: ticket[p] > 0 => \A q \in 1..NumProcs: \/ ~choosing[q]
                                                                 \/ /\ ticket[q] = 0
                                                                    \/ ticket[q] > ticket[p]
                                                                    \/ /\ ticket[q] = ticket[p]
                                                                       \/ p < q

Spec == 
    Init /\ [][Next]_<<ticket, choosing>> /\ WF_next(<<ticket, choosing>>)

Init ==
    \A p \in 1..NumProcs: ticket[p] = 0 /\ ~choosing[p]

Next ==
    \/ \E p \in 1..NumProcs: ChooseTicketAction(p)
    \/ \E p \in 1..NumProcs: WaitForTurnAction(p)
    \/ \E p \in 1..NumProcs: ReleaseTicketAction(p)

ChooseTicketAction(p) ==
    /\ choosing[p]
    /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ticket[q] : q \in 1..NumProcs})]
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]

WaitForTurnAction(p) ==
    /\ ~(\A q \in 1..NumProcs: \/ ~choosing[q]
                                 \/ ticket[q] = 0
                                 \/ ticket[q] > ticket[p]
                                 \/ /\ ticket[q] = ticket[p]
                                    \/ p < q)
    /\ UNCHANGED <<ticket, choosing>>

ReleaseTicketAction(p) ==
    /\ ticket[p] > 0
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED choosing

WF_next(vars) == 
    \A state \in StateSpace: 
        \/ ~(\E p \in 1..NumProcs: ChooseTicketAction(p))
        \/ ~(\E p \in 1..NumProcs: WaitForTurnAction(p))
        \/ ~(\E p \in 1..NumProcs: ReleaseTicketAction(p))

StateSpace == [ticket : [1..NumProcs -> 0..MaxNum], choosing : [1..NumProcs -> BOOLEAN]]

=============================================================================