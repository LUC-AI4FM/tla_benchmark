```
MODULE PlusCalTranslation
EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
  Algorithm, 
  Procedures, 
  Processes, 
  Statements, 
  FairnessOption

VARIABLES 
  spec,
  termination,
  init,
  next,
  variables,
  invariants,
  tempVariables,
  tempInvariants

Init ==
  /\ spec = << >>
  /\ termination = FALSE
  /\ init = << >>
  /\ next = << >>
  /\ variables = {}
  /\ invariants = {}
  /\ tempVariables = {}
  /\ tempInvariants = {}

Next ==
  /\ IF FairnessOption = "NoFairness"
    THEN 
      /\ spec' = Append(spec, "NoFairness")
      /\ termination' = termination
      /\ init' = init
      /\ next' = next
      /\ variables' = variables
      /\ invariants' = invariants
      /\ tempVariables' = tempVariables
      /\ tempInvariants' = tempInvariants
  ELSE IF FairnessOption = "WeakFairnessProcess"
    THEN 
      /\ spec' = Append(spec, "WeakFairnessProcess")
      /\ termination' = termination
      /\ init' = init
      /\ next' = next
      /\ variables' = variables
      /\ invariants' = invariants
      /\ tempVariables' = tempVariables
      /\ tempInvariants' = tempInvariants
  ELSE IF FairnessOption = "WeakFairnessNext"
    THEN 
      /\ spec' = Append(spec, "WeakFairnessNext")
      /\ termination' = termination
      /\ init' = init
      /\ next' = next
      /\ variables' = variables
      /\ invariants' = invariants
      /\ tempVariables' = tempVariables
      /\ tempInvariants' = tempInvariants
  ELSE IF FairnessOption = "StrongFairnessProcess"
    THEN 
      /\ spec' = Append(spec, "StrongFairnessProcess")
      /\ termination' = termination
      /\ init' = init
      /\ next' = next
      /\ variables' = variables
      /\ invariants' = invariants
      /\ tempVariables' = tempVariables
      /\ tempInvariants' = tempInvariants
  ELSE 
    /\ spec' = spec
    /\ termination' = termination
    /\ init' = init
    /\ next' = next
    /\ variables' = variables
    /\ invariants' = invariants
    /\ tempVariables' = tempVariables
    /\ tempInvariants' = tempInvariants

Spec == Init /\ [][Next]_variables

THEOREM Spec => []termination
```