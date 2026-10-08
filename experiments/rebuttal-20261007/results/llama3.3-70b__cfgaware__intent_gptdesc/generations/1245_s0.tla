---------------------------- MODULE Translator ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Object, Any

VARIABLE ast, state, pc, callStack, procTable, varTable, labelTable

TypeInvariant == 
  /\ ast \in Seq(Any)
  /\ state \in [Object -> Any]
  /\ pc \in Nat
  /\ callStack \in Seq(Nat)
  /\ procTable \in [Nat -> Any]
  /\ varTable \in [Object -> Any]
  /\ labelTable \in [Object -> Nat]

Init ==
  /\ ast = << >>
  /\ state = [x \in Object |-> Undefined]
  /\ pc = 0
  /\ callStack = <<
  /\ procTable = [p \in Nat |-> Undefined]
  /\ varTable = [v \in Object |-> Undefined]
  /\ labelTable = [l \in Object |-> 0]

Next ==
  /\ IF pc < Len(ast)
    THEN 
      /\ LET statement == ast[pc] IN
        (IF statement.type = "if"
          THEN 
            /\ IF EvaluateCondition(statement.condition, state)
              THEN pc' = pc + 1
              ELSE pc' = FindLabel(statement.elseLabel, labelTable)
          ELSE 
            (IF statement.type = "while"
              THEN 
                /\ IF EvaluateCondition(statement.condition, state)
                  THEN pc' = FindLabel(statement.bodyLabel, labelTable)
                  ELSE pc' = pc + 1
              ELSE 
                (IF statement.type = "call"
                  THEN 
                    /\ callStack' = Append(callStack, pc)
                    /\ procTable' = [procTable EXCEPT ![statement.procId] = state]
                    /\ varTable' = [varTable EXCEPT ![statement.params] = state]
                    /\ pc' = FindLabel(statement.procLabel, labelTable)
                  ELSE 
                    (IF statement.type = "return"
                      THEN 
                        /\ callStack' = Tail(callStack)
                        /\ procTable' = [procTable EXCEPT ![statement.procId] = Undefined]
                        /\ varTable' = [varTable EXCEPT ![statement.params] = Undefined]
                        /\ pc' = Head(callStack) + 1
                      ELSE 
                        (IF statement.type = "goto"
                          THEN pc' = FindLabel(statement.label, labelTable)
                          ELSE 
                            (IF statement.type = "either"
                              THEN 
                                /\ LET choice == ChooseEnabledAction(statement.actions, state) IN
                                  /\ state' = [state EXCEPT ![choice.var] = choice.value]
                                  /\ pc' = pc + 1
                              ELSE 
                                (IF statement.type = "with"
                                  THEN 
                                    /\ LET choice == ChooseEnabledAction(statement.actions, state) IN
                                      /\ state' = [state EXCEPT ![choice.var] = choice.value]
                                      /\ pc' = FindLabel(statement.nextLabel, labelTable)
                                  ELSE 
                                    (pc' = pc + 1))))))
        )
      ELSE 
        /\ pc' = pc

EvaluateCondition(cond, state) == 
  CASE cond.type OF
    "true" => TRUE
    "false" => FALSE
    "var" => state[cond.var]
    "not" => ~EvaluateCondition(cond.arg, state)
    "and" => EvaluateCondition(cond.left, state) /\ EvaluateCondition(cond.right, state)
    "or" => EvaluateCondition(cond.left, state) \/ EvaluateCondition(cond.right, state)
  ESAC

FindLabel(label, labelTable) == 
  IF label \in Dom(labelTable)
  THEN labelTable[label]
  ELSE Error("Undefined label")

ChooseEnabledAction(actions, state) == 
  LET enabledActions == {a \in actions : a.enabled(state)} IN
    IF enabledActions # {}
      THEN Choose(enabledActions)
      ELSE Error("No enabled actions")

Error(msg) == FALSE

Spec == Init /\ [][Next]_state

THEOREM Spec => []TypeInvariant
=============================================================================