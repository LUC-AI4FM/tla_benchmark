---------------------------- MODULE FastMutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE x, y, b, cs

x == 0
y == 0
b == [i \in 1..N |-> FALSE]
cs == {}

Invariant == (cs = {} ∨ ∃ i ∈ 1..N : cs = {i})

Liveness == ◇□(∃ i ∈ 1..N : i ∈ cs)

Next(i) ==
  /\ b[i] = FALSE
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ y' = y
  /\ cs' = cs

Next2(i) ==
  /\ b[i] = TRUE
  /\ x = i
  /\ y ≠ 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ x' = x
  /\ y' = y
  /\ cs' = cs

Next3(i) ==
  /\ b[i] = TRUE
  /\ x = i
  /\ y = 0
  /\ y' = i
  /\ b' = b
  /\ x' = x
  /\ cs' = cs

Next4(i) ==
  /\ b[i] = TRUE
  /\ x ≠ i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ x' = x
  /\ y' = y
  /\ cs' = cs

Next5(i) ==
  /\ b[i] = FALSE
  /\ ∀ j ∈ (1..N \ {i}) : ¬b[j]
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = x
  /\ y' = y
  /\ cs' = cs

Next6(i) ==
  /\ b[i] = TRUE
  /\ x ≠ i
  /\ y ≠ i
  /\ b' = b
  /\ x' = x
  /\ y' = 0
  /\ cs' = cs

Next7(i) ==
  /\ b[i] = TRUE
  /\ x = i
  /\ y = i
  /\ cs' = {i}
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ x' = x
  /\ y' = 0

Spec == 
  /\ (x = 0) ∧ (y = 0) ∧ (b = [i \in 1..N |-> FALSE]) ∧ (cs = {})
  /\ [][\A i ∈ 1..N : 
      (Next(i)) ∨
      (Next2(i)) ∨
      (Next3(i)) ∨
      (Next4(i)) ∨
      (Next5(i)) ∨
      (Next6(i)) ∨
      (Next7(i)) ∨
      (b' = b) ∧ (x' = x) ∧ (y' = y) ∧ (cs' = cs)
    ]
  /\ WF_i∈1..N (\E i ∈ 1..N : 
      (Next(i)) ∨
      (Next2(i)) ∨
      (Next3(i)) ∨
      (Next4(i)) ∨
      (Next5(i)) ∨
      (Next6(i)) ∨
      (Next7(i))
    )
=============================================================================