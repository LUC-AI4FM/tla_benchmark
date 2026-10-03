MODULE Euclid

IMPORTS Integers, Sequences

CONSTANT MaxNum

VARIABLES pc, u_ini, v_ini, u, v, steps

vars == <<pc, u_ini, v_ini, u, v, steps>>

GCD(a,b) == IF b = 0 THEN a ELSE GCD(b, a % b)

--algorithm Euclid
variables u_ini, v_ini, u, v, steps;
begin
  Init:
    u := u_ini; v := v_ini; steps := 0;
  while (u # v) do
    if u > v then
      u := u - v;
      steps := steps + 1
    else
      v := v - u;
      steps := steps + 1
  end while
end Euclid

Spec == Init /\ [][Next]_vars

Termination == WF_vars(Next) => <> (pc = "END")

Invariant == (u >= 1 /\ v >= 1 /\ u <= MaxNum /\ v <= MaxNum) /\
             (pc = "END" => (u = GCD(u_ini, v_ini) /\ v = u))

MaxSteps == MaxNum * MaxNum
ExpectedSteps == steps <= MaxSteps

End MODULE