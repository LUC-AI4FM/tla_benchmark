---------------------------- MODULE PlusCalTranslation ----------------------------
EXTENDS Integers, Sequences

CONSTANT Object
VARIABLE Any

TypeOk(obj) == obj \in Object

(* Representation of abstract syntax trees *)
AST == [type : {"Algorithm" | "Procedure" | "Process" | "LabeledStatement"}, 
        name : String, 
        params : Seq(String), 
        body : Seq(Any)]

TranslateInit(ast) == 
  IF ast.type = "Algorithm"
  THEN <<>> 
  ELSE IF ast.type = "Procedure"
       THEN <<>> 
       ELSE IF ast.type = "Process"
            THEN <<>> 
            ELSE <<>>

TranslateNext(ast) == 
  IF ast.type = "Algorithm"
  THEN <<>> 
  ELSE IF ast.type = "Procedure"
       THEN <<>> 
       ELSE IF ast.type = "Process"
            THEN <<>> 
            ELSE <<>>

TranslateSpec(ast) == 
  IF ast.type = "Algorithm"
  THEN <<>> 
  ELSE IF ast.type = "Procedure"
       THEN <<>> 
       ELSE IF ast.type = "Process"
            THEN <<>> 
            ELSE <<>>

TerminationProperty(ast) == 
  IF ast.type = "Algorithm"
  THEN <<>> 
  ELSE IF ast.type = "Procedure"
       THEN <<>> 
       ELSE IF ast.type = "Process"
            THEN <<>> 
            ELSE <<>>

FairnessOptions == {"NoFairness", "WeakFairnessActions", "WeakFairnessNext", "StrongFairnessActions"}

TranslateFairness(ast, fairness) == 
  CASE fairness OF
    "NoFairness" => <<>>
    "WeakFairnessActions" => <<>>
    "WeakFairnessNext" => <<>>
    "StrongFairnessActions" => <<>>
    OTHER => FALSE
  END

=============================================================================