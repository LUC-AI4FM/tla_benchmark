```tla
MODULE BufferedRandomAccessFile

EXTENDS Integers, Sequences

CONSTANTS
  BufferSize,
  InitialFileLength,
  MaxFileLength

VARIABLES
  fileContents,
  bufferSize,
  bufferStart,
  bufferDirty,
  currentPosition,
  currentBuffer

Init ==
  /\ fileContents = << >>
  /\ bufferSize = BufferSize
  /\ bufferStart = 0
  /\ bufferDirty = FALSE
  /\ currentPosition = 0
  /\ currentBuffer = << >>

Next ==
  \/ SeekStep
  \/ ReadStep
  \/ WriteStep
  \/ FlushStep
  \/ SetLengthStep

SeekStep ==
  /\ \E newPosition \in 0..MaxFileLength :
    /\ currentPosition' = newPosition
    /\ IF newPosition < bufferStart OR newPosition >= bufferStart + bufferSize
      THEN
        /\ IF bufferDirty
          THEN
            /\ fileContents' = [fileContents EXCEPT ![bufferStart .. bufferStart + bufferSize - 1] = currentBuffer]
            /\ bufferDirty' = FALSE
          ELSE
            /\ fileContents' = fileContents
        /\ bufferStart' = newPosition - (newPosition MOD bufferSize)
        /\ currentBuffer' = SubSeq(fileContents, bufferStart', bufferSize)
      ELSE
        /\ fileContents' = fileContents
        /\ bufferStart' = bufferStart
        /\ currentBuffer' = currentBuffer
    /\ bufferSize' = bufferSize
    /\ bufferDirty' = bufferDirty

ReadStep ==
  /\ \E bytesRead \in Nat :
    /\ bytesRead <= MaxFileLength - currentPosition
    /\ IF currentPosition < bufferStart OR currentPosition >= bufferStart + bufferSize
      THEN
        /\ IF bufferDirty
          THEN
            /\ fileContents' = [fileContents EXCEPT ![bufferStart .. bufferStart + bufferSize - 1] = currentBuffer]
            /\ bufferDirty' = FALSE
          ELSE
            /\ fileContents' = fileContents
        /\ bufferStart' = currentPosition - (currentPosition MOD bufferSize)
        /\ currentBuffer' = SubSeq(fileContents, bufferStart', bufferSize)
      ELSE
        /\ fileContents' = fileContents
        /\ bufferStart' = bufferStart
        /\ currentBuffer' = currentBuffer
    /\ currentPosition' = currentPosition + bytesRead
    /\ bufferSize' = bufferSize
    /\ bufferDirty' = bufferDirty

WriteStep ==
  /\ \E bytesWritten \in Nat :
    /\ bytesWritten <= MaxFileLength - currentPosition
    /\ IF currentPosition < bufferStart OR currentPosition >= bufferStart + bufferSize
      THEN
        /\ IF bufferDirty
          THEN
            /\ fileContents' = [fileContents EXCEPT ![bufferStart .. bufferStart + bufferSize - 1] = currentBuffer]
            /\ bufferDirty' = FALSE
          ELSE
            /\ fileContents' = fileContents
        /\ bufferStart' = currentPosition - (currentPosition MOD bufferSize)
        /\ currentBuffer' = SubSeq(fileContents, bufferStart', bufferSize)
      ELSE
        /\ fileContents' = fileContents
        /\ bufferStart' = bufferStart
        /\ currentBuffer' = currentBuffer
    /\ fileContents' = [fileContents EXCEPT ![currentPosition .. currentPosition + bytesWritten - 1] = << >>]
    /\ currentPosition' = currentPosition + bytesWritten
    /\ bufferSize' = bufferSize
    /\ bufferDirty' = TRUE

FlushStep ==
  /\ bufferDirty
  /\ fileContents' = [fileContents EXCEPT ![bufferStart .. bufferStart + bufferSize - 1] = currentBuffer]
  /\ bufferDirty' = FALSE
  /\ currentPosition' = currentPosition
  /\ bufferStart' = bufferStart
  /\ currentBuffer' = currentBuffer
  /\ bufferSize' = bufferSize

SetLengthStep ==
  /\ \E newLength \in 0..MaxFileLength :
    /\ fileContents' = IF newLength < Len(fileContents)
                    THEN Take(newLength, fileContents)
                    ELSE Append(fileContents, Repeat(<< >>, newLength - Len(fileContents)))
    /\ currentPosition' = IF newLength < currentPosition
                        THEN newLength
                        ELSE currentPosition
    /\ bufferStart' = 0
    /\ currentBuffer' = << >>
    /\ bufferSize' = BufferSize
    /\ bufferDirty' = FALSE

Spec ==
  /\ Init
  /\ [][Next]_fileContents
  /\ WF_Vars(SeekStep)
  /\ WF_Vars(ReadStep)
  /\ WF_Vars(WriteStep)
  /\ SF_Vars(FlushStep)

THEOREM Spec => []BufferBoundsInvariant
THEOREM Spec => []BufferCoherence
THEOREM Spec => []UnbufferedRegionCoherence
THEOREM Spec => []DirtyTrackingCorrectness

BufferBoundsInvariant ==
  currentPosition >= bufferStart /\ currentPosition < bufferStart + bufferSize

BufferCoherence ==
  \A pos \in Nat :
    (pos >= bufferStart /\ pos < bufferStart + bufferSize)
      => fileContents[pos] = currentBuffer[pos - bufferStart]

UnbufferedRegionCoherence ==
  \A pos \in Nat :
    (pos < bufferStart \/ pos >= bufferStart + bufferSize)
      => fileContents[pos] = fileContents'[pos]

DirtyTrackingCorrectness ==
  bufferDirty <=> \E pos \in Nat :
    (pos >= bufferStart /\ pos < bufferStart + bufferSize
      /\ currentBuffer[pos - bufferStart] # fileContents[pos])
```