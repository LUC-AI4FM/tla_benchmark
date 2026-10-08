---- MODULE ConcurrentIncrement ----

VARIABLES x

(*--algorithm concurrent_increment
variables x = 0;

process (A \in {"P1", "P2"})
begin
    with pc \in { "start", "increment", "done" }
    do
        if pc = "start" then
            await TRUE;
            x := x + 1;
            pc := "increment";
        else if pc = "increment" then
            await TRUE;
            pc := "done"
        end if;
    od;
end process;

end algorithm;*)

Spec == /\ Init
        /\ [][Next]_<<x>>
        /\ WF_<<x>>(Next)

Init == x = 0

Next ==
    \/ \E A \in {"P1", "P2"}: PC[A] = "start" /\ x' = x + 1 /\ PC' = [PC EXCEPT ![A] = "increment"]
    \/ \E A \in {"P1", "P2"}: PC[A] = "increment" /\ x' = x /\ PC' = [PC EXCEPT ![A] = "done"]

====