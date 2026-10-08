----------------------------- MODULE SimpleDeterministicTransformer -----------------------------

EXTENDS Integers, TLC

CONSTANTS
  CTRLSET, \* A finite set of five integers serving as both control values and vector indices
  DistVal, \* The distinguished value in CTRLSET that triggers the update
  Fixed     \* The fixed integer written into the vector at index DistVal

ASSUME
  /\ CTRLSET \subseteq Int
  /\ Cardinality(CTRLSET) = 5
  /\ DistVal \in CTRLSET
  /\ Fixed \in Int

VARIABLES
  ctrl, \* The control value (remains constant)
  vec   \* The vector of integer counters, indexed by CTRLSET

vars == << ctrl, vec >>

TypeOK ==
  /\ ctrl \in CTRLSET
  /\ vec \in [CTRLSET -> Int]

State ==
  [ ctrl: CTRLSET,
    vec: [CTRLSET -> Int]
  ]

Init ==
  /\ ctrl \in CTRLSET
  /\ vec = [ i \in CTRLSET |-> 0 ]

Update(v, c) ==
  IF c = DistVal
    THEN [v EXCEPT ![DistVal] = Fixed]
    ELSE v

Next ==
  /\ ctrl' = ctrl
  /\ vec' = Update(vec, ctrl)

Spec ==
  Init /\ []Next

\* Temporal properties required to hold for every behavior of Spec:

Prop_ControlNeverChanges ==
  [](ctrl' = ctrl)

Prop_VectorEntriesAlwaysIntegers ==
  [](vec \in [CTRLSET -> Int])

Prop_NoSpontaneousChangeExceptAsSpecified ==
  [](vec' = Update(vec, ctrl))

Prop_UpdateWhenControlEqualsDistinguished ==
  [](ctrl = DistVal => vec'[DistVal] = Fixed)

Prop_NoChangeWhenControlNotDistinguished ==
  []((ctrl # DistVal) => vec' = vec)

================================================================================