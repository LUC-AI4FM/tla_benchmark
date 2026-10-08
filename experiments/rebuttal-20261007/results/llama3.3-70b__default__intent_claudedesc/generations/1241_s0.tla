```tla
MODULE PlusCalTranslation
EXTENDS Integers, Sequences, TLC

CONSTANTS Alg, FairnessOption
VARIABLES spec, procSet, init, next, termination

Init ==
  /\ spec = <<>>
  /\ procSet = {}
  /\ init = <<>>
  /\ next = <<>>
  /\ termination = <<>>

Next ==
  /\ IF FairnessOption = "no_fairness"
    THEN TRUE
    ELSE IF FairnessOption = "weak_process_fairness"
      THEN \* weak fairness of all process actions
        <>(\E p \in procSet : <>(next' = [next \cup {p |-> "enabled"}]))
      ELSE IF FairnessOption = "weak_next_fairness"
        THEN \* weak fairness of the entire Next action
          <>(next' = [next \cup {"Next" |-> "enabled"}])
        ELSE IF FairnessOption = "strong_process_fairness"
          THEN \* strong fairness of all process actions
            [](\E p \in procSet : <>(next' = [next \cup {p |-> "enabled"}]))
          ELSE FALSE

Translation(alg, fairnessOption) ==
  LET RECURSIVE Translate == 
    CASE alg.type OF
      "uniprocess" => 
        << "MODULE", "UniprocessAlgorithm",
          "EXTENDS", "Integers", "Sequences", "TLC",
          "VARIABLES", "pc", "stack",
          "Init", "==", "pc", "=", 0, "/\", "stack", "=", "<<>>",
          "Next", "==",
            IF pc = 0 THEN 
              Translate(alg.body)
            ELSE 
              FALSE,
          "Termination", "==", "<>", "pc", "=", -1
        >>
      "multiprocess" => 
        << "MODULE", "MultiprocessAlgorithm",
          "EXTENDS", "Integers", "Sequences", "TLC",
          "CONSTANTS", "ProcSet",
          "VARIABLES", "pc", "stack",
          "Init", "==",
            /\ pc = [i \in ProcSet |-> 0],
            /\ stack = [i \in ProcSet |-> <<>>],
          "Next", "==",
            \/ \E p \in ProcSet : 
              IF pc[p] = 0 THEN 
                Translate(alg.body)
              ELSE 
                FALSE,
          "Termination", "==", "<>", "\A p \in ProcSet : pc[p]", "=", -1
        >>
      "procedure" => 
        << "Procedure", alg.name, "(",
          SequenceToCommaList(alg.params), ")",
          "BEGIN",
          Indent(Translate(alg.body)),
          "END"
        >>
      "process" => 
        << "Process", alg.name, "(",
          SequenceToCommaList(alg.params), ")",
          "BEGIN",
          Indent(Translate(alg.body)),
          "END"
        >>
      "labeled_statement" => 
        << alg.label, ":",
          Translate(alg.statement)
        >>
      "while_loop" => 
        << "WHILE", Translate(alg.condition),
          "DO",
          Indent(Translate(alg.body)),
          "END"
        >>
      "if_either_with" => 
        << "IF", Translate(alg.condition),
          "THEN",
          Indent(Translate(alg.thenBranch)),
          "ELSE",
          Indent(Translate(alg.elseBranch))
        >>
      "assignment" => 
        << alg.variable, ":=", Translate(alg.value)
        >>
      "call" => 
        << "CALL", alg.procedureName,
          SequenceToCommaList(alg.arguments)
        >>
      "return" => 
        << "RETURN"
        >>
      "call_return_combination" => 
        << "CALL_RETURN_COMBINATION",
          alg.procedureName, SequenceToCommaList(alg.arguments)
        >>
      "goto" => 
        << "GOTO", alg.label
        >>
      "when" => 
        << "WHEN", Translate(alg.condition),
          "THEN",
          Indent(Translate(alg.body))
        >>
      "print" => 
        << "PRINT", SequenceToCommaList(alg.arguments)
        >>
      "assert" => 
        << "ASSERT", Translate(alg.condition)
        >>
      "skip" => 
        << "SKIP"
        >>
    END
  IN
    Translate(alg)

Spec ==
  /\ Translation(Alg, FairnessOption)
  /\ Init
  /\ []Next

THEOREM Spec => Termination
```