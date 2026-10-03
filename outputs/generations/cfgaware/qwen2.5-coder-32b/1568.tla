------------------------------- MODULE BakeryAlgorithm -------------------------------

CONSTANTS NumProcs, MaxTicket

VARIABLES choosing, number, in_cs

(*--algorithm bakery
variables choosing = [p \in 1..NumProcs -> FALSE],
          number   = [p \in 1..NumProcs -> 0];

process p \in 1..NumProcs
begin
    while TRUE do
        choosing[p] := TRUE;
        number[p] := 1 + Max({number[q] : q \in 1..NumProcs});
        choosing[p] := FALSE;

        await \A q \in 1..NumProcs: \/ ~choosing[q]
                                   \/ \/ number[q] = 0
                                      \/ /\ number[q] > number[p]
                                         \/ /\ number[q] = number[p]
                                            \/ q < p;
        
        in_cs[p] := TRUE;

        await FALSE; (* Critical Section *)

        in_cs[p] := FALSE;
        number[p] := 0;
    end while;
end process
*)

Spec == 
    /\ Init
    /\ [][Next]_<<choosing, number, in_cs>>
    /\ WF_next(<<choosing, number, in_cs>>)

Init ==
    /\ choosing = [p \in 1..NumProcs -> FALSE]
    /\ number   = [p \in 1..NumProcs -> 0]
    /\ in_cs    = [p \in 1..NumProcs -> FALSE]

Next ==
    \/ \E p \in 1..NumProcs: Choose(p)
    \/ \E p \in 1..NumProcs: EnterCS(p)
    \/ \E p \in 1..NumProcs: ExitCS(p)

Choose(p) ==
    /\ choosing[p] = FALSE
    /\ number' = [number EXCEPT ![p] = 1 + Max({number[q] : q \in 1..NumProcs})]
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ in_cs' = in_cs

EnterCS(p) ==
    /\ choosing[p] = FALSE
    /\ number[p] > 0
    /\ \A q \in 1..NumProcs: \/ ~choosing[q]
                               \/ \/ number[q] = 0
                                  \/ /\ number[q] > number[p]
                                     \/ /\ number[q] = number[p]
                                        \/ q < p
    /\ in_cs' = [in_cs EXCEPT ![p] = TRUE]
    /\ choosing' = choosing
    /\ number' = number

ExitCS(p) ==
    /\ in_cs[p] = TRUE
    /\ in_cs' = [in_cs EXCEPT ![p] = FALSE]
    /\ number' = [number EXCEPT ![p] = 0]
    /\ choosing' = choosing

WF_next(vars) == 
    WF_vars(Choose, vars)
    /\ WF_vars(EnterCS, vars)
    /\ WF_vars(ExitCS, vars)

WF_vars(act, vars) ==
    \A s \in State: act EnabledIn(s) => <act>_<<vars>>_EnabledIn(s)

EnabledIn(action) ==
    \/ action = Choose
    \/ action = EnterCS
    \/ action = ExitCS

State == [choosing: [1..NumProcs -> BOOLEAN], number: [1..NumProcs -> 0..MaxTicket], in_cs: [1..NumProcs -> BOOLEAN]]

Invariant ==
    /\ \A p, q \in 1..NumProcs: \/ ~in_cs[p] \/ ~in_cs[q] \/ p = q
    /\ \A p \in 1..NumProcs: number[p] \leq MaxTicket

=============================================================================