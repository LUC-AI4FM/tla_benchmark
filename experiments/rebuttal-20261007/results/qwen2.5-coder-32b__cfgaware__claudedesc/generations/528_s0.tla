---- MODULE SimpleAlgorithm ----

CONSTANTS pc

VARIABLES x, y

(*--algorithm SimpleAlgorithm
variables x = {"a", "b"}, y = <<1, 2, 3>>, pc = "Start";

begin
Lbl_1:
    with
        x := x \cup {"c"},
        y := [y EXCEPT ![1] = 4]
    do
        print x;
        print y;
    end with;
    pc := "Done";
Terminating:
    while TRUE do
        skip;
    end while;
end algorithm;*)

Init == /\ x = {"a", "b"}
        /\ y = <<1, 2, 3>>
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
             /\ x' = x \cup {"c"}
             /\ y' = [y EXCEPT ![1] = 4]
             /\ UNCHANGED pc
        \/ /\ pc = "Start"
             /\ PrintT(x)
             /\ PrintT(y)
             /\ pc' = "Done"
             /\ UNCHANGED <<x, y>>
        \/ /\ pc = "Done"
             /\ pc' = "Done"
             /\ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x, y, pc>>

Termination == <>(pc = "Done")

====