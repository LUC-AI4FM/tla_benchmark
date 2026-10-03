---- MODULE HourClock ----
EXTENDS Integers

VARIABLES hr

(*
--algorithm hclock
variable hr \in 1..12;
begin
  H:
    while TRUE do
      if hr = 12 then
        hr := 1;
      else
        hr := hr + 1;
      end if;
    end while;
end algorithm;
*)

HCini == hr \in 1..12

HCnxt == IF hr = 12
           THEN hr' = 1
           ELSE hr' = hr + 1

Spec == HCini /\ [][HCnxt]_hr

HC == Spec

THEOREM Spec => []HCini

========================