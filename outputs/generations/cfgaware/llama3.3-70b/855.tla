---------------------------- MODULE prisoners_and_switches ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Prisoner
VARIABLE p2, p3, count, visited

TypeOK == (p2 \in [Prisoner -> {<<"up">>, <<"down">>}]) /\
          (p3 \in [Prisoner -> {<<"up">>, <<"down">>}]) /\
          (count \in 0..Cardinality(Prisoner)) /\
          (visited \subseteq Prisoner)

CountInvariant == count <= Cardinality({p \in Prisoner : p2[p] = <<"up">>})

Spec == Initialize /\ [][Next]_<<p2, p3, count, visited>>
Initialize == (p2 = [p \in Prisoner |-> <<"down">>] ) /\
              (p3 = [p \in Prisoner |-> <<"down">>] ) /\
              (count = 0) /\
              (visited = {})

Next == \E p \in Prisoner :
        IF p = "counter" THEN
          count' = IF p2["A"] = <<"up">> THEN count + 1 ELSE count
          p2' = [p2 EXCEPT !["A"] = <<"down">>]
          p3' = p3
          visited' = visited \cup {p}
        ELSE
          p2' = [p2 EXCEPT !["A"] = IF p2["A"] = <<"up">> THEN <<"down">> ELSE <<"up">>]
          p3' = [p3 EXCEPT !["B"] = IF p3["B"] = <<"up">> THEN <<"down">> ELSE <<"up">>]
          count' = count
          visited' = visited \cup {p}
        END

Safety == []<>(visited = Prisoner) => [](count = Cardinality(Prisoner))

Liveness == <>[](visited = Prisoner)

THEOREM Spec => []TypeOK /\ Safety /\ Liveness
=============================================================================