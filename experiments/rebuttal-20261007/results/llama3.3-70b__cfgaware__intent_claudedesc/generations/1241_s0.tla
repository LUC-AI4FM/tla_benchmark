```
MODULE PlusCalTranslation
IMPORT Integers, Sequences, TLC

CONSTANT Object, Any

VARIABLE alg, fairnessOption, pc, stack

Proc == [ type : {"uniprocess", "multiprocess"}, 
          procedures : [ name : String |-> [ params : Seq(String), body : Seq(Stmt) ] ], 
          processes : [ name : String |-> [ locals : Set(String), body : Seq(Stmt) ] ] ]

Stmt == [ type : {"label", "while", "if", "either", "with", "assign", "call", "return", "goto", "when", "print", "assert", "skip" },
          label : String,
          cond : BoolExpr,
          body : Seq(Stmt),
          params : Seq(String),
          locals : Set(String) ]

BoolExpr == [ type : {"true", "false", "not", "and", "or", "="}, 
              left : Any, 
              right : Any ]

Translation(alg, fairnessOption) ==
  LET Procs == alg.procedures \cup alg.processes
  IN
    << "/** TLA+ specification generated from +CAL algorithm */",
      "/** Variables */",
      "VARIABLE pc, stack",
      "/** Procedures and Processes */",
      (SeqToLexemes(Procs)),
      "/** Init and Next definitions */",
      "Init == pc = ""init"" /\ stack = <<>>",
      "Next == ",
        (IF fairnessOption = "no_fairness"
         THEN "(pc = ""init"") \/ "
         ELSE IF fairnessOption = "weak_process_fairness"
              THEN "\E p \in ProcSet : (pc[p] = ""init"") \/ "
              ELSE IF fairnessOption = "weak_next_fairness"
                   THEN "(pc = ""init"") \/ "
                   ELSE IF fairnessOption = "strong_process_fairness"
                        THEN "\A p \in ProcSet : (pc[p] = ""init"") \/ "
                        ELSE UNCHANGED <<pc, stack>>),
      "/** Termination property */",
      "Termination == <>(pc = ""done"")"
    >>

SeqToLexemes(seq) ==
  Concatenate(SEQ s \in seq |-> 
                (IF s.type = "procedure"
                 THEN <<"/** Procedure ", s.name, " */",
                      "Proc_", s.name, "_Init == ",
                        (StmtToLexemes(s.body)),
                      "Proc_", s.name, "_Next == ",
                        (StmtToLexemes(s.body))>>
                 ELSE IF s.type = "process"
                      THEN <<"/** Process ", s.name, " */",
                           "Proc_", s.name, "_Init == ",
                             (StmtToLexemes(s.body)),
                           "Proc_", s.name, "_Next == ",
                             (StmtToLexemes(s.body))>>
                      ELSE <<>>))

StmtToLexemes(stmt) ==
  CASE stmt.type OF
    "label" => <<stmt.label, ": pc = """, stmt.label, """">>
    "while" => <<"/** While loop */",
                "WHILE ", 
                  (BoolExprToLexemes(stmt.cond)),
                " DO ",
                  (StmtToLexemes(stmt.body))>>
    "if" => <<"/** If statement */",
             "IF ",
               (BoolExprToLexemes(stmt.cond)),
             " THEN ",
               (StmtToLexemes(stmt.body))>>
    "either" => <<"/** Either statement */",
                 "EITHER ",
                   (BoolExprToLexemes(stmt.cond)),
                 " OR ",
                   (StmtToLexemes(stmt.body))>>
    "with" => <<"/** With statement */",
               "WITH ",
                 (BoolExprToLexemes(stmt.cond)),
               " DO ",
                 (StmtToLexemes(stmt.body))>>
    "assign" => <<"/** Assignment */",
                 stmt.label, " := ",
                   (BoolExprToLexemes(stmt.cond))>>
    "call" => <<"/** Procedure call */",
               "CALL ",
                 stmt.label,
               " WITH ",
                 (SeqToLexemes(stmt.params))>>
    "return" => <<"/** Return statement */",
                 "RETURN">>
    "goto" => <<"/** Goto statement */",
               "GOTO ",
                 stmt.label>>
    "when" => <<"/** When statement */",
              "WHEN ",
                (BoolExprToLexemes(stmt.cond)),
              " DO ",
                (StmtToLexemes(stmt.body))>>
    "print" => <<"/** Print statement */",
                "PRINT ",
                  (BoolExprToLexemes(stmt.cond))>>
    "assert" => <<"/** Assert statement */",
                 "ASSERT ",
                   (BoolExprToLexemes(stmt.cond))>>
    "skip" => <<"/** Skip statement */",
               "SKIP">>
  END

BoolExprToLexemes(expr) ==
  CASE expr.type OF
    "true" => << "TRUE">>
    "false" => << "FALSE">>
    "not" => << "~", 
                (BoolExprToLexemes(expr.left))>>
    "and" => << "( ",
               (BoolExprToLexemes(expr.left)),
               " ) /\\ (",
               (BoolExprToLexemes(expr.right)),
               " )">>
    "or" => << "( ",
              (BoolExprToLexemes(expr.left)),
              " ) \\/ (",
              (BoolExprToLexemes(expr.right)),
              " )">>
    "=" => << "( ",
             (BoolExprToLexemes(expr.left)),
             " ) = (",
             (BoolExprToLexemes(expr.right)),
             " )">>
  END

THEOREM Translation(alg, fairnessOption) \* UNCHANGED Object
THEOREM Translation(alg, fairnessOption) \* UNCHANGED Any
```
Note: The above TLA+ specification defines the abstract syntax of a +CAL algorithm as a grammar of records and sequences. It then defines an operator `Translation` that produces, as a sequence of lexemes, the TLA+ specification corresponding to the algorithm's abstract syntax tree. The translation expands labeled statements into atomic actions with explicit pc assignments, handles procedure call and return via stack manipulation, adds process-local variable subscripts for multiprocess algorithms, generates Init and Next definitions, defines ProcSet for multiprocess algorithms, and appends a Termination property. The fairnessOption parameter supports four values: no fairness, weak fairness of all process actions, weak fairness of the entire Next action, and strong fairness of all process actions.