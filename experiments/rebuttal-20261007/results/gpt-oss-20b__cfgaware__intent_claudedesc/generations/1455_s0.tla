------------------------------ MODULE SubsetPowersetTest ------------------------------
EXTENDS Naturals, FiniteSets

VARIABLES flag

(* Boolean expression that verifies all subset‑equality properties *)
AllTests == 
  (SUBSET(1..3) \subseteq SUBSET(1..5)) /\ 
  ~(SUBSET(1..5) \subseteq SUBSET(1..3)) /\
  (SUBSET((1..4) \ {2}) \subseteq SUBSET(1..4)) /\ 
  ~(SUBSET(1..4) \subseteq SUBSET((1..4) \ {2})) /\
  (SUBSET({1,2}) \subseteq SUBSET({1,2,3})) /\ 
  ~(SUBSET({1,2,3}) \subseteq SUBSET({1,2})) /\
  (SUBSET(∅) \subseteq SUBSET(∅)) /\ 
  (SUBSET(∅) \subseteq SUBSET({1})) /\ 
  ~(SUBSET({1}) \subseteq SUBSET(∠)) /\ 
  (SUBSET({1}) \subseteq SUBSET(Nat))

Init == flag = AllTests

Next == UNCHANGED <<flag>>

Inv == flag = TRUE /\ flag \in BOOLEAN

Spec == Init /\ [][Next]_<<flag>> /\ Inv

=============================================================================