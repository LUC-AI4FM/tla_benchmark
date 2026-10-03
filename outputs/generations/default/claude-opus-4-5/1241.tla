---------------------------- MODULE PlusCalToTLA ----------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

CONSTANTS
    \* AST Node Types
    AlgorithmNode, ProcedureNode, ProcessNode, LabeledStmtNode,
    AssignNode, IfNode, WhileNode, CallNode, ReturnNode, GotoNode,
    PrintNode, AssertNode, SkipNode, WithNode, AwaitNode,
    
    \* Fairness options
    NoFairness, WeakFairProcess, WeakFairNext, StrongFairProcess,
    
    \* Expression types
    VarExpr, ConstExpr, BinOpExpr, UnaryOpExpr,
    
    \* Maximum values for model checking
    MaxVars, MaxProcs, MaxLabels, MaxStmts,
    
    \* Special tokens
    NIL

VARIABLES
    \* The input AST
    ast,
    \* The output lexeme sequence (TLA+ specification)
    output,
    \* Current translation state
    translationState,
    \* Error flag
    error,
    \* Fairness setting for generated spec
    fairnessOption,
    \* Variables declared in the algorithm
    declaredVars,
    \* Procedures defined
    procedures,
    \* Processes defined  
    processes,
    \* Labels collected
    labels,
    \* Current position in translation
    position

vars == <<ast, output, translationState, error, fairnessOption, 
          declaredVars, procedures, processes, labels, position>>

-----------------------------------------------------------------------------
\* Grammar predicates for legal AST nodes

IsVarDecl(node) ==
    /\ node # NIL
    /\ "name" \in DOMAIN node
    /\ "init" \in DOMAIN node

IsExpr(node) ==
    \/ node = NIL
    \/ /\ "type" \in DOMAIN node
       /\ node.type \in {VarExpr, ConstExpr, BinOpExpr, UnaryOpExpr}

IsStmt(node) ==
    /\ node # NIL
    /\ "type" \in DOMAIN node
    /\ node.type \in {AssignNode, IfNode, WhileNode, CallNode, 
                      ReturnNode, GotoNode, PrintNode, AssertNode,
                      SkipNode, WithNode, AwaitNode}

IsLabeledStmt(node) ==
    /\ node # NIL
    /\ "type" \in DOMAIN node
    /\ node.type = LabeledStmtNode
    /\ "label" \in DOMAIN node
    /\ "stmts" \in DOMAIN node
    /\ \A i \in 1..Len(node.stmts) : IsStmt(node.stmts[i])

IsProcedure(node) ==
    /\ node # NIL
    /\ "type" \in DOMAIN node
    /\ node.type = ProcedureNode
    /\ "name" \in DOMAIN node
    /\ "params" \in DOMAIN node
    /\ "body" \in DOMAIN node

IsProcess(node) ==
    /\ node # NIL
    /\ "type" \in DOMAIN node
    /\ node.type = ProcessNode
    /\ "name" \in DOMAIN node
    /\ "id" \in DOMAIN node
    /\ "body" \in DOMAIN node

IsAlgorithm(node) ==
    /\ node # NIL
    /\ "type" \in DOMAIN node
    /\ node.type = AlgorithmNode
    /\ "name" \in DOMAIN node
    /\ "variables" \in DOMAIN node
    /\ "procedures" \in DOMAIN node
    /\ "processes" \in DOMAIN node
    /\ \A i \in 1..Len(node.variables) : IsVarDecl(node.variables[i])
    /\ \A i \in 1..Len(node.procedures) : IsProcedure(node.procedures[i])
    /\ \A i \in 1..Len(node.processes) : IsProcess(node.processes[i])

-----------------------------------------------------------------------------
\* Lexeme sequence operations

EmptyOutput == <<>>

Append1(seq, lex) == Append(seq, lex)

AppendSeq(seq1, seq2) == seq1 \o seq2

Newline == "\n"
Space == " "
Indent(n) == [i \in 1..n |-> Space]

-----------------------------------------------------------------------------
\* Translation helper operators

\* Generate variable declarations for TLA+
TranslateVarDecl(varDecl) ==
    <<varDecl.name>>

TranslateVarDecls(varDecls) ==
    IF Len(varDecls) = 0 
    THEN <<>>
    ELSE LET first == TranslateVarDecl(varDecls[1])
             rest == TranslateVarDecls(Tail(varDecls))
         IN AppendSeq(first, rest)

\* Generate Init predicate
GenerateInit(algNode) ==
    LET header == <<"Init", " ", "==", Newline>>
        varInits == [i \in 1..Len(algNode.variables) |->
                     <<Space, Space, "/\\", Space, 
                       algNode.variables[i].name, Space, "=", Space,
                       "InitValue", Newline>>]
    IN AppendSeq(header, 
                 IF Len(varInits) = 0 
                 THEN <<"TRUE", Newline>>
                 ELSE varInits[1])

\* Generate action for a labeled statement
GenerateLabelAction(labeledStmt, procName) ==
    <<labeledStmt.label, Space, "==", Newline,
      Space, Space, "/\\", Space, "pc", Space, "=", Space, 
      "\"", labeledStmt.label, "\"", Newline>>

\* Generate process actions
GenerateProcessActions(procNode) ==
    IF "body" \notin DOMAIN procNode 
    THEN <<>>
    ELSE IF Len(procNode.body) = 0 
         THEN <<>>
         ELSE GenerateLabelAction(procNode.body[1], procNode.name)

\* Generate Next predicate
GenerateNext(algNode) ==
    LET header == <<Newline, "Next", Space, "==", Newline>>
        \* Collect all labeled statements from all processes
        processActions == 
            IF Len(algNode.processes) = 0 
            THEN <<Space, Space, "FALSE", Newline>>
            ELSE <<Space, Space, "\\E", Space, "self", Space, "\\in", Space,
                   "ProcSet", Space, ":", Space, "TRUE", Newline>>
    IN AppendSeq(header, processActions)

\* Generate fairness conditions based on option
GenerateFairness(algNode, fairOpt) ==
    CASE fairOpt = NoFairness -> <<>>
      [] fairOpt = WeakFairNext -> 
            <<Newline, "Fairness", Space, "==", Space, 
              "WF_vars(Next)", Newline>>
      [] fairOpt = WeakFairProcess ->
            <<Newline, "Fairness", Space, "==", Space,
              "\\A", Space, "self", Space, "\\in", Space, "ProcSet", Space, ":",
              Space, "WF_vars(Process(self))", Newline>>
      [] fairOpt = StrongFairProcess ->
            <<Newline, "Fairness", Space, "==", Space,
              "\\A", Space, "self", Space, "\\in", Space, "ProcSet", Space, ":",
              Space, "SF_vars(Process(self))", Newline>>
      [] OTHER -> <<>>

\* Generate Spec definition
GenerateSpec(algNode, fairOpt) ==
    LET base == <<Newline, "Spec", Space, "==", Space, 
                  "Init", Space, "/\\", Space, "[][Next]_vars">>
        fairness == IF fairOpt = NoFairness 
                    THEN <<Newline>>
                    ELSE <<Space, "/\\", Space, "Fairness", Newline>>
    IN AppendSeq(base, fairness)

\* Generate Termination property
GenerateTermination == 
    <<Newline, "Termination", Space, "==", Space,
      "<>", Space, "(", "\\A", Space, "self", Space, "\\in", Space, 
      "ProcSet", Space, ":", Space, "pc[self]", Space, "=", Space,
      "\"Done\"", ")", Newline>>

\* Main translation function
TranslateAlgorithm(algNode, fairOpt) ==
    LET moduleHeader == <<"----", Space, "MODULE", Space, 
                          algNode.name, Space, "----", Newline,
                          "EXTENDS", Space, "Integers,", Space, 
                          "Sequences,", Space, "TLC", Newline, Newline>>
        varsSection == <<"VARIABLES", Space, "pc", Newline, Newline>>
        initSection == GenerateInit(algNode)
        nextSection == GenerateNext(algNode)
        fairSection == GenerateFairness(algNode, fairOpt)
        specSection == GenerateSpec(algNode, fairOpt)
        termSection == GenerateTermination
        footer == <<Newline, "====