------------------------------- MODULE FischerTimedMutualExclusion -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES request, timer, in_critical_section

(*--algorithm FischerTimedMutualExclusion
variables 
  request = [i \in 1..N -> FALSE], 
  timer   = [i \in 1..N -> Infinity], 
  in_critical_section = [i \in 1..N -> FALSE];

process (p \in 1..N) \begin {
  while TRUE \do
    request[p] := TRUE;
    with (q \in 1..N) \ {
      if q /= p /\ request[q] then 
        await timer[q] >= timer[p];
        timer[p] := timer[p] + Delta;
      fi;
    };
    in_critical_section[p] := TRUE;
    (* Critical Section *)
    in_critical_section[p] := FALSE;
    request[p] := FALSE;
    with (q \in 1..N) \ {
      if q /= p then
        await timer[q] >= timer[p];
        timer[q] := timer[q] + Delta;
      fi;
    };
  od;
}

process Ticker = 
  while TRUE \do
    with (p \in 1..N) \ {
      if request[p] then
        timer[p] := timer[p] - Epsilon;
      fi;
    };
  od;

end algorithm *)
====