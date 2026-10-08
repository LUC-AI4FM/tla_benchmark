------------------------------- MODULE PlusCalToTLA --------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    -- Constants representing the abstract syntax tree nodes
    AlgorithmNodes, ProcedureNodes, ProcessNodes, StatementNodes,
    Labels, Actions, FairnessOptions

VARIABLES 
    ast, tlaSpec, fairness

Init == 
    /\ ast \in [ "type" |-> "Algorithm", "procedures" |-> SUBSET ProcedureNodes, "processes" |-> SUBSET ProcessNodes ]
    /\ tlaSpec = << >>
    /\ fairness \in FairnessOptions

Next ==
    \/ /\ ast["type"] = "Algorithm"
       /\ tlaSpec' = Append(tlaSpec, TranslateAlgorithm(ast))
       /\ fairness' = fairness
    \/ /\ ast["type"] = "Procedure"
       /\ tlaSpec' = Append(tlaSpec, TranslateProcedure(ast))
       /\ fairness' = fairness
    \/ /\ ast["type"] = "Process"
       /\ tlaSpec' = Append(tlaSpec, TranslateProcess(ast))
       /\ fairness' = fairness

TranslateAlgorithm(a) ==
    LET procedures == a["procedures"]
        processes  == a["processes"]
    IN << "---- MODULE GeneratedSpec ----", 
         "EXTENDS Naturals, Sequences, FiniteSets",
         "CONSTANTS " ^ (StringSet(procedures)),
         "VARIABLES " ^ (StringSet(processes)),
         "Init == TRUE",
         "Next == ",
         "Spec == Init /\ [][Next]_<< " ^ (StringSet(processes)) ^ " >>",
         "Termination == <>[]( \/ " ^ (StringSet(processes)) ^ "' /= " ^ (StringSet(processes))) ^ ")" >>

TranslateProcedure(p) ==
    LET statements == p["statements"]
    IN << "-- Procedure: " ^ p["name"],
         "PROCEDURE " ^ p["name"] ^ "()",
         StringSeq(statements) >>

TranslateProcess(pr) ==
    LET statements == pr["statements"]
        label      == pr["label"]
    IN << "-- Process: " ^ pr["name"],
         "PROCESS " ^ pr["name"],
         "BEGIN",
         IF label \in Labels THEN
             "  " ^ label ^ ":"
         ELSE
             "",
         StringSeq(statements),
         "END" >>

StringSet(s) ==
    STRING (CHOOSE x \in s : x)

StringSeq(seq) ==
    LET f[x] == 
            CASE x["type"] = "Action" -> ActionToString(x)
            []  x["type"] = "Label"  -> LabelToString(x)
            []  TRUE                   -> ""
    IN StringConcat(<< >>, seq, f)

ActionToString(a) ==
    a["action"]

LabelToString(l) ==
    l["label"] ^ ":"

Spec == Init /\ [][Next]_<< ast, tlaSpec, fairness >>

FairnessOptions == {"NoFairness", "WeakFairProcessActions", "WeakFairNext", "StrongFairProcessActions"}

=============================================================================