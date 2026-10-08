--------------------------- MODULE FischerTimed ----------------------------
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES state, timer

(*--------------------------------------------------------------------------*)
(* Initial condition                                                       *)
Init == 
  /\ \A i \in 1..N : state[i] = "Idle"
  /\ \A i \in 1..N : timer[i] = Infinity

(*--------------------------------------------------------------------------*)
(* The PlusCal algorithm translated below                                 *)

-- algorithm FischerTimed
variables
  state = [i \in 1..N |-> "Idle"],
  timer = [i \in 1..N |-> Infinity];

process Ticker {
  while TRUE do
    for i \in 1..N do
      if timer[i] > 0 then
        timer[i] := timer[i] - 1;
    end for;
    skip;
  end while;
}

process P(i) : 1..N {
  while TRUE do
    if state[i] = "Idle" then
       state[i] := "TryingEntry";
       timer[i] := Delta;
    else if state[i] = "TryingEntry" /\ timer[i] = 0 then
      if \A j \in 1..N : (j # i) => state[j] /= "CS" then
        state[i] := "CS";
        timer[i] := Epsilon;
      end if;
    else if state[i] = "CS" /\ timer[i] = 0 then
       state[i] := "Idle";
    else skip;
  end while;
}
end algorithm

(*--------------------------------------------------------------------------*)
(* Safety invariant: no two processes are in the critical section simultaneously *)
NoTwoCS == \A i, j \in 1..N : (i # j) => ~(state[i] = "CS" /\ state[j] = "CS")

(*--------------------------------------------------------------------------*)
(* Liveness property: some process is infinitely often in the CS           *)
InfCS(i) == [] <> (state[i] = "CS")
Liveness == \E i \in 1..N : InfCS(i)

(*--------------------------------------------------------------------------*)
(* Full specification                                                     *)
Spec == Init /\ [][Next]_vars

FullSpec == Spec /\ NoTwoCS

=============================================================================