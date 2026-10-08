------------------------------- MODULE BakeryMutex -------------------------------

CONSTANTS NumProcs, MaxNum

VARIABLES ticket, choosing, inCS

(*--algorithm bakery_mutex
variables 
  ticket = [p \in 1..NumProcs -> 0],
  choosing = [p \in 1..NumProcs -> FALSE],
  inCS = [p \in 1..NumProcs -> FALSE];

process p \in 1..NumProcs
begin
ChooseTicket:
  choosing[p] := TRUE;
  with max_ticket == MAX {ticket[q] : q \in 1..NumProcs} do
    ticket[p] := max_ticket + 1;
  end with;
  choosing[p] := FALSE;

WaitForTurn:
  await \A q \in 1..NumProcs \ {p}: \/ ~choosing[q]
                                 \/ ticket[q] = 0
                                 \/ /\ ticket[q] > ticket[p]
                                    \/ /\ ticket[q] = ticket[p]
                                       /\ q > p;
  
EnterCS:
  inCS[p] := TRUE;

CriticalSection:
  skip; (* Critical section code here *)

ExitCS:
  inCS[p] := FALSE;
  ticket[p] := 0;
end process;
end algorithm*)

Spec == 
  /\ Init
  /\ \A p \in 1..NumProcs: [][Next]_<<p>>
  /\ WF_next

Init ==
  /\ ticket = [p \in 1..NumProcs -> 0]
  /\ choosing = [p \in 1..NumProcs -> FALSE]
  /\ inCS = [p \in 1..NumProcs -> FALSE]

Next ==
  \/ \E p \in 1..NumProcs: ChooseTicket(p)
  \/ \E p \in 1..NumProcs: WaitForTurn(p)
  \/ \E p \in 1..NumProcs: EnterCS(p)
  \/ \E p \in 1..NumProcs: CriticalSection(p)
  \/ \E p \in 1..NumProcs: ExitCS(p)

ChooseTicket(p) ==
  /\ choosing[p]
  /\ \E max_ticket \in 0..MaxNum: 
     /\ max_ticket = MAX {ticket[q] : q \in 1..NumProcs}
     /\ ticket' = [ticket EXCEPT ![p] = max_ticket + 1]
     /\ choosing' = [choosing EXCEPT ![p] = FALSE]

WaitForTurn(p) ==
  /\ ~inCS[p]
  /\ \A q \in 1..NumProcs \ {p}: \/ ~choosing[q]
                                 \/ ticket[q] = 0
                                 \/ /\ ticket[q] > ticket[p]
                                    \/ /\ ticket[q] = ticket[p]
                                       /\ q > p

EnterCS(p) ==
  /\ WaitForTurn(p)
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]

CriticalSection(p) ==
  /\ inCS[p]
  /\ UNCHANGED <<ticket, choosing>>

ExitCS(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]

WF_next == 
  WF_vars(<<ticket, choosing, inCS>>, Next)

Invariant ==
  \/ \A p \in 1..NumProcs: ~inCS[p]
  \/ \E p \in 1..NumProcs: /\ inCS[p]
                           /\ \A q \in 1..NumProcs \ {p}: ~inCS[q]

=============================================================================