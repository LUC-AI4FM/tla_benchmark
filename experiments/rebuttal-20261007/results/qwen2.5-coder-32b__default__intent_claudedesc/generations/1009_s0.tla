------------------------------- MODULE BufferedRandomAccessFile -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    BufferSize,  \* Size of the in-memory buffer
    MaxFileSize  \* Maximum possible size of the file

VARIABLES 
    CurrentPos,  \* Current position in the file
    FileLength,  \* Length of the file
    BufferStart, \* Starting offset of the buffer in the file
    BufferData,  \* Data stored in the buffer (sequence of bytes)
    IsDirty      \* Flag indicating if the buffer is dirty

Init == 
    /\ CurrentPos = 0
    /\ FileLength = 0
    /\ BufferStart = 0
    /\ BufferData = << >>
    /\ IsDirty = FALSE

Seek(newPos) ==
    \/ /\ newPos >= 0
       /\ newPos <= FileLength
       /\ (IsDirty -> Flush)
       /\ CurrentPos' = newPos
       /\ (newPos < BufferStart \/ newPos >= BufferStart + Len(BufferData))
          -> (BufferStart' = newPos - (newPos % BufferSize) 
              /\ BufferData' = << >> 
              /\ IsDirty' = FALSE)

Read(bytesToRead) ==
    \* Calculate the end position of the read operation
    LET endPos == CurrentPos + bytesToRead IN
    \/ /\ endPos <= FileLength
       /\ (endPos > BufferStart + Len(BufferData))
          -> (Flush 
              /\ BufferStart' = CurrentPos - (CurrentPos % BufferSize)
              /\ BufferData' = GetFileContent(BufferStart', Min(BufferSize, FileLength - BufferStart'))
              /\ IsDirty' = FALSE
              /\ CurrentPos' = endPos
              /\ ReadResult = SubSeq(BufferData', 1 + (CurrentPos % BufferSize), bytesToRead))
       /\ (endPos <= BufferStart + Len(BufferData))
          -> (CurrentPos' = endPos
              /\ ReadResult = SubSeq(BufferData, 1 + (CurrentPos % BufferSize), bytesToRead))

Write(bytesToWrite) ==
    \* Calculate the end position of the write operation
    LET endPos == CurrentPos + Len(bytesToWrite) IN
    \/ /\ endPos <= MaxFileSize
       /\ (endPos > BufferStart + Len(BufferData))
          -> (Flush 
              /\ BufferStart' = CurrentPos - (CurrentPos % BufferSize)
              /\ BufferData' = GetFileContent(BufferStart', Min(BufferSize, FileLength - BufferStart'))
              /\ IsDirty' = TRUE
              /\ CurrentPos' = endPos
              /\ UpdateBuffer(BufferData', 1 + (CurrentPos % BufferSize), bytesToWrite))
       /\ (endPos <= BufferStart + Len(BufferData))
          -> (CurrentPos' = endPos
              /\ IsDirty' = TRUE
              /\ UpdateBuffer(BufferData, 1 + (CurrentPos % BufferSize), bytesToWrite))

Flush ==
    \/ /\ IsDirty
       /\ WriteFileContent(BufferStart, BufferData)
       /\ IsDirty' = FALSE

SetLength(newLength) ==
    \/ /\ newLength >= 0
       /\ newLength <= MaxFileSize
       /\ (IsDirty -> Flush)
       /\ FileLength' = newLength
       /\ (newLength < BufferStart + Len(BufferData))
          -> (BufferData' = SubSeq(BufferData, 1, newLength - BufferStart)
              /\ IsDirty' = TRUE)

Next ==
    \/ \E newPos \in Integers : Seek(newPos)
    \/ \E bytesToRead \in SUBSET Nat : Read(bytesToRead)
    \/ \E bytesToWrite \in Seq(Nat) : Write(bytesToWrite)
    \/ Flush
    \/ \E newLength \in Integers : SetLength(newLength)

Spec ==
    /\ Init
    /\ [][Next]_<<CurrentPos, FileLength, BufferStart, BufferData, IsDirty>>
    /\ WF_next(Next)

\* Invariants

LogicalConsistency ==
    /\ CurrentPos >= 0
    /\ CurrentPos <= FileLength
    /\ Len(BufferData) <= BufferSize
    /\ BufferStart + Len(BufferData) <= MaxFileSize

BufferBoundsInvariant ==
    /\ CurrentPos >= BufferStart
    /\ CurrentPos < BufferStart + Len(BufferData)

BufferCoherence ==
    \A pos \in {BufferStart .. BufferStart + Len(BufferData) - 1} :
        GetFileContent(pos, 1) = SubSeq(BufferData, 1 + (pos % BufferSize), 1)

UnbufferedRegionCoherence ==
    \A pos \notin {BufferStart .. BufferStart + Len(BufferData) - 1} :
        GetFileContent(pos, 1) = GetUnderlyingFileContent(pos, 1)

DirtyTrackingCorrectness ==
    \/ /\ IsDirty
       /\ (\E pos \in {BufferStart .. BufferStart + Len(BufferData) - 1} :
               GetFileContent(pos, 1) # SubSeq(BufferData, 1 + (pos % BufferSize), 1))
    \/ /\ ~IsDirty
       /\ (\A pos \in {BufferStart .. BufferStart + Len(BufferData) - 1} :
               GetFileContent(pos, 1) = SubSeq(BufferData, 1 + (pos % BufferSize), 1))

Refinement ==
    \* This is a placeholder for the refinement property which would require
    \* modeling a simple random access file and comparing behaviors.

InvariantRestoration ==
    \/ /\ IsDirty -> Flush
    \/ /\ ~IsDirty -> Seek(CurrentPos)

\* Fairness

WF_next(Next) == 
    WF_vars(<<CurrentPos, FileLength, BufferStart, BufferData, IsDirty>>, Next)

=============================================================================