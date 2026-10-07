MODULE PowerSetSubsetTest
EXTENDS Integers

VARIABLE b

Init == 
  /\ b = TRUE

Next ==
  /\ b' = (\power(1..23) \subseteq \power(1..42)) /\
          ~( \power(1..42) \subseteq \power(1..23)) /\
          (\power(2..42) \subseteq \power(1..42)) /\
          ~( \power(1..42) \subseteq \power(2..42)) /\
          (\power({1,2,3}) \subseteq \power({1,2,3,4})) /\
          ~( \power({1,2,3,4}) \subseteq \power({1,2,3})) /\
          (\power({}) \subseteq \power({})) /\
          (\power({}) \subseteq \power({1})) /\
          (\power({1}) \subseteq \power(Int)) /\
          (\power({1}) \subseteq \power(Nat))

Inv == b = TRUE /\ b \in BOOLEAN

Spec == Init /\ [][Next]_b /\ []Inv