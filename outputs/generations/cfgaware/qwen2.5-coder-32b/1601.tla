------------------------------- MODULE FischerTimedMutualExclusion -------------------------------

CONSTANTS N, Epsilon, Delta, Infinity

VARIABLES requestTime, inCS, timer, turn

(*--algorithm FischerTimedMutualExclusion
variables requestTime = [p \in 1..N -> Infinity],
          inCS = [p \in 1..N -> FALSE],
          timer = [p \in 1..N -> Infinity],
          turn;

process Ticker =
  while TRUE do
    await TRUE;
    with p \in 1..N do
      if timer[p] /= Infinity then
        timer[p] := timer[p] - 1;
      end if;
    end with;
end process

process Process \in 1..N
begin
  while TRUE do
    requestTime[self] := MAX(requestTime) + 1;
    turn := self;
    await (\A q \in 1..N \ {self}: 
             (requestTime[q] = Infinity \/ 
              (requestTime[q] > requestTime[self]) \/ 
              (requestTime[q] = requestTime[self] /\ q = turn)));
    timer[self] := Delta;
    inCS[self] := TRUE;
    
    (* Critical Section *)
    skip;

    inCS[self] := FALSE;
    requestTime[self] := Infinity;
    await \E q \in 1..N: timer[q] < Epsilon;
  end while
end process

end algorithm *)

Spec == /\ Init
        /\ [][Next]_<<requestTime, inCS, timer, turn>>
        /\ WF_[Next]_<<requestTime, inCS, timer, turn>>

Init == /\ requestTime = [p \in 1..N -> Infinity]
        /\ inCS = [p \in 1..N -> FALSE]
        /\ timer = [p \in 1..N -> Infinity]
        /\ turn \in 1..N

Next == \/ TickerAction
        \/ ProcessAction

TickerAction ==
    /\ \E p \in 1..N: timer[p] /= Infinity
    /\ \A p \in 1..N: 
         (timer'[p] = IF timer[p] /= Infinity THEN timer[p] - 1 ELSE timer[p])
    /\ UNCHANGED <<requestTime, inCS, turn>>

ProcessAction ==
    \/ \E self \in 1..N:
        /\ requestTime[self]' = MAX(requestTime) + 1
        /\ turn' = self
        /\ \A q \in 1..N \ {self}: 
             (requestTime[q] = Infinity \/ 
              (requestTime[q] > requestTime'[self]) \/ 
              (requestTime[q] = requestTime'[self] /\ q = turn'))
        /\ timer[self]' = Delta
        /\ inCS[self]' = TRUE
        /\ \A p \in 1..N \ {self}: UNCHANGED <<requestTime[p], inCS[p], timer[p]>>
        /\ UNCHANGED turn
    \/ \E self \in 1..N:
        /\ inCS[self]
        /\ inCS'[self] = FALSE
        /\ requestTime'[self] = Infinity
        /\ \A p \in 1..N \ {self}: UNCHANGED <<requestTime[p], inCS[p]>>
        /\ timer'[self] = IF timer[self] /= Infinity THEN timer[self] - 1 ELSE timer[self]
        /\ UNCHANGED turn
    \/ \E self \in 1..N:
        /\ ~inCS[self]
        /\ \A q \in 1..N: 
             (requestTime[q] = Infinity \/ 
              (requestTime[q] > requestTime[self]) \/ 
              (requestTime[q] = requestTime[self] /\ q = turn))
        /\ timer'[self] = IF timer[self] /= Infinity THEN timer[self] - 1 ELSE timer[self]
        /\ UNCHANGED <<requestTime, inCS, turn>>

Invariant == \A p, q \in 1..N: 
                 (p # q => ~inCS[p] \/ ~inCS[q])

Liveness ==
    <>[] (\E p \in 1..N: inCS[p])

=============================================================================