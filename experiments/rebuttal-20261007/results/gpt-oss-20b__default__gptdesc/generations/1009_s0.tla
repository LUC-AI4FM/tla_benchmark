------------------------------ MODULE BufferedFile ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS
    BufSize,
    ArbitrarySymbol,
    SymbolSet

VARIABLES
    fileContent,
    buffer,
    pos,
    bufStart,
    dirty

(* Helper definitions *)
FileLength == Len(fileContent)
BufEnd == Min(bufStart + BufSize - 1, FileLength)

InBuffer(i) == (i >= bufStart /\ i <= BufEnd)
BufferIndex(i) == i - bufStart + 1
BufIndices == {i \in 1..FileLength : InBuffer(i)}

(* Safety invariant *)
Inv ==
    /\ pos \in 0..FileLength
    /\ bufStart \in 1..(FileLength+1)
    /\ dirty \in BOOLEAN
    /\ Len(buffer) = Min(BufSize, FileLength - bufStart + 1)
    /\ IF NOT dirty THEN
           \A i \in BufIndices : buffer[BufferIndex(i)] = fileContent[i]
       ELSE TRUE

(* Initial state *)
Init ==
    /\ fileContent = <<>>
    /\ buffer = <<>>
    /\ pos = 0
    /\ bufStart = 1
    /\ dirty = FALSE

Seek(offset) ==
    /\ offset \in 0..FileLength
    /\ NOT dirty
    /\ pos' = offset
    /\ bufStart' = 1 + (offset \div BufSize) * BufSize
    /\ buffer' = SubSeq(fileContent, bufStart', Min(bufStart'+BufSize-1, FileLength))
    /\ dirty' = FALSE
    /\ UNCHANGED <<fileContent>>

Read(n) ==
    /\ n \in Nat
    /\ NOT dirty
    /\ InBuffer(pos+1)
    /\ readData == SubSeq(buffer, BufferIndex(pos+1), Min(BufferIndex(pos+1)+n-1, Len(buffer)))
    /\ pos' = pos + Len(readData)
    /\ UNCHANGED <<fileContent, buffer, bufStart, dirty>>

Write(seq) ==
    /\ seq \in Seq(SymbolSet)
    /\ NOT dirty
    /\ InBuffer(pos+1)
    /\ newBuf == SubSeq(buffer, 1, BufferIndex(pos+1)-1) 
                \o seq
                \o SubSeq(buffer, BufferIndex(pos)+Len(seq), Len(buffer))
    /\ buffer' = newBuf
    /\ dirty' = TRUE
    /\ pos' = pos + Len(seq)
    /\ UNCHANGED <<fileContent, bufStart>>

Flush ==
    /\ dirty
    /\ fileContent' = SubSeq(fileContent, 1, bufStart-1) \o buffer \o SubSeq(fileContent, BufEnd+1, FileLength)
    /\ dirty' = FALSE
    /\ UNCHANGED <<buffer, pos, bufStart>>

SetLength(newLen) ==
    /\ newLen \in Nat
    /\ NOT dirty
    /\ IF newLen > FileLength THEN
           fileContent' = fileContent \o Replicate(newLen - FileLength, ArbitrarySymbol)
       ELSE