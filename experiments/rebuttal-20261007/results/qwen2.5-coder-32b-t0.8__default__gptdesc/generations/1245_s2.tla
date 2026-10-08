---- MODULE GlobalNamingPlusCalToTLA ----
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS 
    ActionSet, ProcessNames, Labels

VARIABLES 
    ast, currentAction, processState, labelStack

Init == 
    /\ ast \in Seq(Record)
    /\ currentAction = <<>>
    /\ processState \in [ProcessNames -> Record]
    /\ labelStack \in Seq(Labels)

Next ==
    \/ \E action \in ActionSet : 
        /\ currentAction' = action
        /\ processState' = [processState EXCEPT ![currentAction!process] = TranslateAction(currentAction)]
        /\ labelStack' = ExplodeLabels(currentAction, labelStack)
    \/ \E label \in Labels :
        /\ currentAction' = <<>>
        /\ processState' = processState
        /\ labelStack' = [labelStack EXCEPT <<>> = label]

TranslateAction(action) ==
    CASE action.type = "call" -> CallTranslation(action)
         [] action.type = "return" -> ReturnTranslation(action)
         [] action.type = "goto" -> GotoTranslation(action, labelStack)
         ELSE processState[action.process]

CallTranslation(action) ==
    [processState EXCEPT ![action.process] = AddSubscripts(processState[action.process], action)]

ReturnTranslation(action) ==
    [processState EXCEPT ![action.process] = RemoveSubscripts(processState[action.process])]

GotoTranslation(action, labelStack) ==
    LET nextLabel == Head(labelStack)
    IN  processState[nextLabel.process]

AddSubscripts(state, action) ==
    [v \in DOMAIN state |-> AppendSubscript(v, action)]

RemoveSubscripts(state) ==
    [v \in DOMAIN state |-> RemoveLastSubscript(v)]

AppendSubscript(var, action) ==
    var \o "_" \o ToString(action.id)

RemoveLastSubscript(var) ==
    LET parts == SplitString(var, "_")
    IN  TakeExceptLast(parts)

SplitString(str, delim) ==
    {s \in SUBSEQ(ChopAt(str, FindStr(str, delim)))}

FindStr(str, delim) ==
    CHOOSE i \in DOMAIN str : str[i] = delim

TakeExceptLast(seq) ==
    <<seq[1..Len(seq)-1]>>

ExplodeLabels(action, labelStack) ==
    IF action.type = "goto" 
    THEN [labelStack EXCEPT <<>> = LabelFromAction(action)]
    ELSE labelStack

LabelFromAction(action) ==
    CHOOSE l \in Labels : l.name = action.label

Spec == Init /\ [][Next]_<<currentAction, processState, labelStack>>

FairnessOptions ==
    \/ WF_[Next]_<<currentAction>>
    \/ WF_[\E p \in ProcessNames : ActionForProcess(p)]_<<currentAction>>
    \/ SF_[\E p \in ProcessNames : ActionForProcess(p)]_<<currentAction>>

ActionForProcess(process) == 
    {action \in ActionSet : action.process = process}

Termination ==
    <>(\A action \in ActionSet : currentAction # action)

====