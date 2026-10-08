------------------------------- MODULE CalToTlaTranslator -------------------------------

CONSTANTS 
    \* Placeholder for any object type
    Object,
    
    \* Placeholder for any value
    Any

VARIABLES 
    ast,          \* The abstract syntax tree of the +CAL algorithm
    fairness,     \* Fairness option: "none", "weak_action", "weak_nextstate", "strong_action"
    lexemes       \* Sequence of TLA+ lexemes representing the translated specification

\* Grammar for valid +CAL abstract syntax trees
CalGrammar == 
    [ TYPE : {"uniprocess", "multiprocess"},
      PROCEDURES : << >> \cup [name: STRING -> CalProcedure],
      VARIABLES : << >> \cup [name: STRING -> CalVariable],
      STATEMENTS : << CalStatement >> ]

CalProcedure ==
    [ NAME : STRING,
      PARAMETERS : << >> \cup [name: STRING -> CalParameter],
      BODY : CalBlock ]

CalParameter ==
    [ NAME : STRING,
      TYPE : {"input", "output"} ]

CalVariable ==
    [ NAME : STRING,
      TYPE : {"local", "global"},
      PROCESS : STRING ] \* PROCESS is only relevant for multiprocess algorithms

CalBlock ==
    << CalStatement >> 

CalStatement ==
    [ TYPE : {"assignment", "when", "print", "assert", "skip", "while", "if_either_with", "call", "return", "combined_call_return", "goto"},
      \* Fields vary based on the statement type
      lhs : STRING, 
      rhs : STRING,
      condition : CalExpression,
      body : CalBlock,
      else_body : CalBlock,
      with_body : CalBlock,
      target_label : STRING,
      procedure_name : STRING,
      arguments : << STRING >> ]

CalExpression ==
    [ TYPE : {"variable", "constant", "binary_op"},
      value : STRING,
      op : STRING,
      left : CalExpression,
      right : CalExpression ]

\* Translation operator
Translation(ast, fairness) == 
    LET 
        variable_declarations == GetVariableDeclarations(ast),
        init_predicate == InitPredicate(ast),
        action_definitions == ActionDefinitions(ast),
        next_state_action == NextStateAction(ast),
        spec_formula == SpecFormula(fairness),
        termination_property == TerminationProperty()
    IN
        << "---- MODULE TranslatedSpec ----",
           variable_declarations,
           "====