---------------------------- MODULE Inner ----------------------------
EXTENDS Sequences, Integers

CONSTANTS InitSeq

VARIABLES result, seq

InnerInit ==
    /\ result = 0
    /\ seq = InitSeq

InnerStep ==
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x : x # 1)

InnerNext ==
    InnerStep

InnerSpec ==
    /\ InnerInit
    /\ [][InnerNext]_<<result, seq>>
    /\ WF_<<result, seq>>(InnerStep)

StepEnabled ==
    result = 0

Terminated ==
    ~StepEnabled

EventuallyTerminated ==
    <>[]Terminated

=======================================================================