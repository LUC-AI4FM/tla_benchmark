---- MODULE SimpleCounter ----
EXTENDS Naturals, TLC

VARIABLES x

(*
--algorithm simple_counter
begin
  x := 1;
  while x < 5 do
    x := x + 1;
  end while;
  assert x = 5;
  while TRUE do
    x := x;
  end while;
end algorithm;
*)

Init == x = 1

Next == (x < 5 /\ x' = x + 1)
           \/
        (x = 5 /\ x' = x)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

LivenessProperty == <>([] (x = 5))

THEOREM Spec => LivenessProperty

====