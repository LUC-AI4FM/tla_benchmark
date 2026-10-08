```tla
MODULE BufferedRandomAccessFile

EXTENDS Integers, Sequences, RandomAccessFile

CONSTANTS
  MaxBufferSize,
  ArbitrarySymbol

VARIABLES
  buffer,
  bufferSize,
  fileLength,
  onDiskContents,
  logicalContents

Init ==
  /\ buffer = << >>
  /\ bufferSize = 0
  /\ fileLength = 0
  /\ onDiskContents = << >>
  /\ logicalContents = << >>

Next ==
  /\ (bufferSize' = bufferSize)
  /\ OR
    /\ (buffer' = buffer)
    /\ (fileLength' = fileLength)
    /\ (onDiskContents' = onDiskContents)
    /\ (logicalContents' = logicalContents)
    /\ SeekStep
    /\ ReadStep
    /\ WriteStep
    /\ FlushStep
    /\ SetLengthStep

SeekStep ==
  /\ buffer' = << >>
  /\ bufferSize' = 0
  /\ fileLength' = fileLength
  /\ onDiskContents' = onDiskContents
  /\ logicalContents' = logicalContents

ReadStep ==
  /\ buffer' = Append(buffer, Head(onDiskContents))
  /\ bufferSize' = bufferSize + 1
  /\ fileLength' = fileLength
  /\ onDiskContents' = Tail(onDiskContents)
  /\ logicalContents' = logicalContents

WriteStep ==
  /\ buffer' = Append(buffer, ArbitrarySymbol)
  /\ bufferSize' = bufferSize + 1
  /\ fileLength' = fileLength
  /\ onDiskContents' = onDiskContents
  /\ logicalContents' = Append(logicalContents, ArbitrarySymbol)

FlushStep ==
  /\ buffer' = << >>
  /\ bufferSize' = 0
  /\ fileLength' = fileLength + bufferSize
  /\ onDiskContents' = Append(onDiskContents, buffer)
  /\ logicalContents' = logicalContents

SetLengthStep ==
  /\ buffer' = << >>
  /\ bufferSize' = 0
  /\ fileLength' = fileLength + bufferSize
  /\ onDiskContents' = Append(onDiskContents, buffer)
  /\ logicalContents' = Take(logicalContents, fileLength)

Spec ==
  Init /\ [][Next]_<<buffer, bufferSize, fileLength, onDiskContents, logicalContents>>

THEOREM Spec => []TypeInvariant
THEOREM Spec => []BufferSizeInvariant
THEOREM Spec => []BufferContentsInvariant

TypeInvariant ==
  /\ buffer \in Seq(ArbitrarySymbol)
  /\ bufferSize \in Nat
  /\ fileLength \in Nat
  /\ onDiskContents \in Seq(ArbitrarySymbol)
  /\ logicalContents \in Seq(ArbitrarySymbol)

BufferSizeInvariant ==
  bufferSize <= MaxBufferSize

BufferContentsInvariant ==
  (bufferSize = 0) => (buffer = << >>)

Fairness == SF_VARIABLES(buffer, bufferSize, fileLength, onDiskContents, logicalContents)

=============================================================================
TLC Configuration
=============================================================================

CONSTANT
  ModelCheckingConstants =
    [MaxBufferSize |-> 10,
     ArbitrarySymbol |-> "arb"]

INVARIANT
  TypeInvariant

PROPERTIES
  Spec => []TypeInvariant
  Spec => []BufferSizeInvariant
  Spec => []BufferContentsInvariant

FAIRNESS
  Fairness

SYMMETRY
  fileLength, onDiskContents, logicalContents

ALIASING
  buffer, bufferSize
```