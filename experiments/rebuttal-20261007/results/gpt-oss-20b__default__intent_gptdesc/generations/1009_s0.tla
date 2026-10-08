MODULE BufferedFile
EXTENDS Naturals, Sequences, TLC

CONSTANTS BufferSize \* Positive integer > 0

(* Types *)
SUBTYPE BYTE == {b \in Nat : b <= 255}

VARIABLES fileLen, ptr, bufStart, bufEnd, bufContent, dirty, underlying

(* Helper definitions *)
InBuffer(i) == (bufStart <= i /\ i < bufEnd)

UnderlyingDomainInv == DOMAIN underlying = 0..fileLen-1
BufSizeInv          == bufEnd = MIN(bufStart + BufferSize, fileLen)
DirtyInvariant ==
    IF dirty THEN TRUE
    ELSE \A i \in [bufStart .. bufEnd-1] : underlying[i] = bufContent[i - bufStart]

Init ==
    /\ fileLen = 0
    /\ ptr = 0
    /\ bufStart = 0
    /\ bufEnd = 0
    /\ bufContent = [i \in 0..BufferSize-1 |-> 0]
    /\ dirty = FALSE
    /\ underlying = [ ]

(* Actions *)

Seek ==
    \E offset \in 0..fileLen :
        IF InBuffer(offset) THEN
            ptr' = offset
        ELSE
           