------------------------------- MODULE Bakery -------------------------------

CONSTANTS NumProcs, MaxNum

VARIABLES choosing, number, nextProc, maxima, localReads, criticalSection

(*--algorithm bakery
variables 
  choosing = [p \in 1..NumProcs -> FALSE],
  number   = [p \in 1..NumProcs -> 0],
  nextProc = 1,
  maxima   = 0,
  localReads = [p \in 1..NumProcs -> <<>>];

process p \in 1..NumProcs
begin
Entry:
    choosing[p] := TRUE;
    maxima := \E q \in 1..NumProcs : maxima \/ number[q];
    number[p] := maxima + 1;
    choosing[p] := FALSE;

    nextProc := p;
    while (\A q \in 1..NumProcs \ {p} :
             (choosing[q] \/ 
              (number[q] # 0) /\ (<<number[q], q>> << number[p], p>>)))
        do
            skip;
    
    localReads[p] := <<number[q] : q \in 1..NumProcs>>;
    nextProc := 1;

CriticalSection:
    criticalSection := {p};

Exit:
    number[p] := 0;
end process;

end algorithm*)

Spec == 
  /\ Init
  /\ [][Next]_<<choosing, number, nextProc, maxima, localReads, criticalSection>>
  /\ WF_next(<<choosing, number, nextProc, maxima, localReads, criticalSection>>)

Init ==
  /\ choosing = [p \in 1..NumProcs -> FALSE]
  /\ number   = [p \in 1..NumProcs -> 0]
  /\ nextProc = 1
  /\ maxima   = 0
  /\ localReads = [p \in 1..NumProcs -> <<>>]
  /\ criticalSection = {}

Next ==
  \/ \E p \in 1..NumProcs : Entry(p)
  \/ \E p \in 1..NumProcs : CriticalSection(p)
  \/ \E p \in 1..NumProcs : Exit(p)

Entry(p) ==
  \/ /\ choosing[p] = FALSE
     /\ maxima' = (\E q \in 1..NumProcs : maxima \/ number[q])
     /\ number' = [number EXCEPT ![p] = maxima + 1]
     /\ choosing' = [choosing EXCEPT ![p] = TRUE]
  \/ /\ choosing[p] = TRUE
     /\ choosing' = [choosing EXCEPT ![p] = FALSE]

CriticalSection(p) ==
  criticalSection' = {p}

Exit(p) ==
  number' = [number EXCEPT ![p] = 0]

WF_next(vars) == 
  WF_vars(Init, Next, vars)

Invariant ==
  \/ criticalSection = {}
  \/ \A p1, p2 \in criticalSection : p1 = p2

=============================================================================