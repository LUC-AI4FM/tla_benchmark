---------------------------- MODULE OldPlusCal ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Object, Any

VARIABLE ast, fairness

SetOfSeqs == { s \in Seq(Any) : Len(s) > 0 }

(* Grammar of +CAL ASTs *)
Alg == [ type : {"uniprocess" | "multiprocess"},
         procedures : SetOfSeqs,
         processes : SetOfSeqs,
         vars : SetOfSeqs,
         statements : SetOfSeqs ]

Procedure == [ name : String, params : SetOfSeqs, body : Seq(Any) ]
Process == [ name : String, locals : SetOfSeqs, body : Seq(Any) ]
VarDecl == [ name : String, type : {"int" | "bool"} ]
LabeledStmt == [ label : String, stmt : Any ]
WhileLoop == [ cond : Any, body : Seq(Any) ]
LabelSeq == [ labels : SetOfSeqs, stmts : SetOfSeqs ]
SimpleStmt == [ type : { "assign" | "if" | "either" | "with" | "when" | "print" | "assert" | "skip" },
                args : SetOfSeqs ]

Call == [ proc : String, args : SetOfSeqs ]
Return == [ value : Any ]
Goto == [ label : String ]

(* Translation from +CAL AST to TLA+ *)
Translation(alg, fairnessOption) ==
  LET FullyExplodeSeq(seq) == 
    IF seq[1] = "while"
    THEN Concatenate(
           << "While",
             seq[2],
             "{",
             FullyExplodeSeq(seq[3]),
             "}"
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "if"
    THEN Concatenate(
           << "If",
             seq[2],
             "{",
             FullyExplodeSeq(seq[3]),
             "}",
             "Else",
             "{",
             FullyExplodeSeq(seq[4]),
             "}"
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "either"
    THEN Concatenate(
           << "Either",
             seq[2],
             "{",
             FullyExplodeSeq(seq[3]),
             "}",
             "Or",
             "{",
             FullyExplodeSeq(seq[4]),
             "}"
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "with"
    THEN Concatenate(
           << "With",
             seq[2],
             "{",
             FullyExplodeSeq(seq[3]),
             "}"
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "when"
    THEN Concatenate(
           << "When",
             seq[2],
             "{",
             FullyExplodeSeq(seq[3]),
             "}"
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "print"
    THEN Concatenate(
           << "Print",
             seq[2]
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "assert"
    THEN Concatenate(
           << "Assert",
             seq[2]
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE IF seq[1] = "skip"
    THEN Concatenate(
           << "Skip"
           >>,
           FullyExplodeSeq(Tail(seq))
         )
    ELSE seq
  IN
  LET Explode(stmt) ==
    IF stmt[1] = "assign"
    THEN << "Assign",
            stmt[2],
            ":=",
            stmt[3]
          >>
    ELSE IF stmt[1] = "call"
    THEN << "Call",
            stmt[2],
            "(",
            stmt[3],
            ")"
          >>
    ELSE IF stmt[1] = "return"
    THEN << "Return",
            stmt[2]
          >>
    ELSE IF stmt[1] = "goto"
    THEN << "Goto",
            stmt[2]
          >>
  IN
  LET Init == << "Init",
              ":=",
              "{",
              "pc",
              ":=",
              "\"start\"",
              ";",
              "stack",
              ":=",
              "\"[]\""
            >>
  IN
  LET Next == 
    IF fairnessOption = "wf"
    THEN Concatenate(
           << "Next",
             ":=",
             "{",
             FullyExplodeSeq(alg.statements),
             "}"
           >>,
           << "WF_vars",
             "(",
             alg.vars,
             ")"
           >>
         )
    ELSE IF fairnessOption = "wfNext"
    THEN Concatenate(
           << "Next",
             ":=",
             "{",
             FullyExplodeSeq(alg.statements),
             "}"
           >>,
           << "WF_Next",
             "(",
             alg.vars,
             ")"
           >>
         )
    ELSE IF fairnessOption = "sf"
    THEN Concatenate(
           << "Next",
             ":=",
             "{",
             FullyExplodeSeq(alg.statements),
             "}"
           >>,
           << "SF_vars",
             "(",
             alg.vars,
             ")"
           >>
         )
    ELSE << "Next",
            ":=",
            "{",
            FullyExplodeSeq(alg.statements),
            "}"
          >>
  IN
  LET Spec == << "Spec",
              ":=",
              "{",
              Init,
              ";",
              Next
            >>
  IN
  LET ProcSet == << "ProcSet",
                  ":=",
                  "{",
                  alg.procedures
                >>
  IN
  LET vars == << "vars",
               ":=",
               "{",
               alg.vars
             >>
  IN
  LET Termination == << "Termination",
                        ":=",
                        "{",
                        "pc",
                        "=",
                        "\"end\""
                      >>
  IN
  Concatenate(
    Init,
    Next,
    Spec,
    ProcSet,
    vars,
    Termination
  )

ASSUME Translation(ast, fairness)
=============================================================================