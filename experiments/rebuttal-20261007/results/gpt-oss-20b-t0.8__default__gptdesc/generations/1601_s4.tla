MODULE FischerTimed
EXTENDS Naturals, Sequences

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES state, timer

(*--------------------------------------------------------------------*)
(* PlusCal algorithm *)
\*--algorithm FischerTimed
variables state, timer;

process tick {
  while TRUE do
    for i \in 1..N do
      if timer[i] > 0 then
        timer' := [timer EXCEPT ![i] = timer[i]-1];
      else
        skip;
    end;
  end;
}

proc i in 1..N {
  while TRUE do
    case state[i] of
      "Idle" ->
        if TRUE then
          state' := [state EXCEPT ![i] = "Trying"];
          timer' := [timer EXCEPT ![i] = Delta];
        end;
      "Trying" ->
        if (timer[i] <= Epsilon) /\ (\A j \in 1..N : i # j => state[j] # "Critical") then
          state' := [state EXCEPT ![i] = "Critical"];
        end;
      "Critical" ->
        if TRUE then
          state' := [state EXCEPT ![i] = "Idle"];
          timer' := [timer EXCEPT ![i] = Infinity];
        end;
    esac;
  end;
}
\*--end

(*--------------------------------------------------------------------*)
vars == <<state, timer>>

Init ==
  /\ \A i \in 1..N : state[i] = "Idle"
  /\ \A i \in 1..N : timer[i] = Infinity

Next == Next

MutualExclusion ==
  \A i, j \in 1..N :
    (i # j) => ~(state[i] = "Critical" /\ state[j] = "Critical")

Liveliness == \E i \in 1..N : []<> (state[i] = "Critical")

Spec == Init /\ [][Next]_vars /\ MutualExclusion

LTLSPEC Liveliness
--------------------------------------------------------------------