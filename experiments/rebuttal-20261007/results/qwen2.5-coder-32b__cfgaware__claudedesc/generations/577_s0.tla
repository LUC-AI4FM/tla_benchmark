------------------------------- MODULE MCAltInit --------------------------------

EXTENDS MCMultiNodeReads

CONSTANTS HistoryLimit, ViewLimit

VARIABLES ledger, history, requests, responses, committed, invalidated, sequenceNumber, viewNumber

(*--algorithm AltInitSpec
variables 
    ledger = [1 |-> <<>>, 2 |-> <<>>], 
    history = [{request: "req1", response: "res1", committed: TRUE}, {request: "req2", response: "res2", committed: TRUE}],
    requests = {},
    responses = {},
    committed = {"tx1", "tx2"},
    invalidated = {},
    sequenceNumber = 3,
    viewNumber = 3
end algorithm*)

InitAlt == 
    /\ ledger = [1 |-> <<>>, 2 |-> <<>>]
    /\ history = [{request: "req1", response: "res1", committed: TRUE}, {request: "req2", response: "res2", committed: TRUE}]
    /\ requests = {}
    /\ responses = {}
    /\ committed = {"tx1", "tx2"}
    /\ invalidated = {}
    /\ sequenceNumber = 3
    /\ viewNumber = 3

MCSpecMultiNodeReadsAlt == Spec(InitAlt, MCNextMultiNodeReadsAction)

=============================================================================