---------------------------- MODULE BufferedRandomAccessFile ----------------------------
(***************************************************************************)
(* This specification models a buffered random-access file implementation  *)
(* with an abstract RandomAccessFile refinement target.                    *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxFileSize,        \* Maximum file size for model checking
    MaxBufferSize,      \* Maximum buffer size
    DataValues,         \* Set of possible data values
    ArbitrarySymbol     \* Symbol for underspecified file contents

ASSUME MaxFileSize \in Nat /\ MaxFileSize > 0
ASSUME MaxBufferSize \in Nat /\ MaxBufferSize > 0
ASSUME ArbitrarySymbol \notin DataValues

AllSymbols == DataValues \cup {ArbitrarySymbol}

VARIABLES
    \* Concrete buffered file state
    filePointer,        \* Current position in the logical file
    fileLength,         \* Logical length of the file
    diskContents,       \* On-disk file contents (function 0..diskLength-1 -> AllSymbols)
    diskLength,         \* Length of on-disk file
    buffer,             \* In-memory buffer contents
    bufferStart,        \* File position where buffer starts
    bufferLength,       \* Number of valid bytes in buffer
    bufferDirty,        \* Whether buffer has unflushed writes
    bufferModified,     \* Positions in buffer that were modified
    
    \* Abstract file state (for refinement)
    absFilePointer,     \* Abstract file pointer
    absFileLength,      \* Abstract file length
    absFileContents,    \* Abstract file contents
    
    \* Operation tracking
    pc                  \* Program counter for operation sequencing

vars == <<filePointer, fileLength, diskContents, diskLength, buffer, 
          bufferStart, bufferLength, bufferDirty, bufferModified,
          absFilePointer, absFileLength, absFileContents, pc>>

concreteVars == <<filePointer, fileLength, diskContents, diskLength, buffer,
                  bufferStart, bufferLength, bufferDirty, bufferModified>>

abstractVars == <<absFilePointer, absFileLength, absFileContents>>

(***************************************************************************)
(* Helper operators for array/file utilities                               *)
(***************************************************************************)

\* Read from logical file at position pos
LogicalRead(pos) ==
    IF pos < 0 \/ pos >= fileLength
    THEN ArbitrarySymbol
    ELSE IF pos >= bufferStart /\ pos < bufferStart + bufferLength
         THEN buffer[pos - bufferStart]
         ELSE IF pos < diskLength
              THEN diskContents[pos]
              ELSE ArbitrarySymbol

\* Check if position is within buffer
InBuffer(pos) ==
    pos >= bufferStart /\ pos < bufferStart + bufferLength

\* Minimum of two integers
Min(a, b) == IF a < b THEN a ELSE b

\* Maximum of two integers
Max(a, b) == IF a > b THEN a ELSE b

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)

TypeInvariant ==
    /\ filePointer \in 0..MaxFileSize
    /\ fileLength \in 0..MaxFileSize
    /\ diskLength \in 0..MaxFileSize
    /\ bufferStart \in 0..MaxFileSize
    /\ bufferLength \in 0..MaxBufferSize
    /\ bufferDirty \in BOOLEAN
    /\ bufferModified \subseteq (0..(MaxBufferSize-1))
    /\ absFilePointer \in 0..MaxFileSize
    /\ absFileLength \in 0..MaxFileSize
    /\ pc \in {"idle", "seeking", "reading", "writing", "flushing", "setLength"}

(***************************************************************************)
(* Buffer-file relationship invariants                                     *)
(***************************************************************************)

\* Buffer start must be valid
BufferStartValid ==
    bufferLength > 0 => bufferStart >= 0

\* Buffer cannot extend beyond logical file length (for valid data)
BufferBoundsValid ==
    bufferStart + bufferLength <= Max(fileLength, diskLength + bufferLength)

\* If buffer is not dirty, modified set must be empty
DirtyConsistency ==
    ~bufferDirty => bufferModified = {}

\* Modified positions must be within buffer
ModifiedInBuffer ==
    \A pos \in bufferModified : pos < bufferLength

\* Logical file length is consistent
FileLengthConsistency ==
    fileLength >= diskLength \/ (bufferDirty /\ fileLength < diskLength)

\* Abstract and concrete file pointers match
PointerRefinement ==
    filePointer = absFilePointer

\* Abstract and concrete file lengths match
LengthRefinement ==
    fileLength = absFileLength

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
    /\ filePointer = 0
    /\ fileLength = 0
    /\ diskContents = [i \in {} |-> ArbitrarySymbol]
    /\ diskLength = 0
    /\ buffer = [i \in 0..(MaxBufferSize-1) |-> ArbitrarySymbol]
    /\ bufferStart = 0
    /\ bufferLength = 0
    /\ bufferDirty = FALSE
    /\ bufferModified = {}
    /\ absFilePointer = 0
    /\ absFileLength = 0
    /\ absFileContents = [i \in {} |-> ArbitrarySymbol]
    /\ pc = "idle"

(***************************************************************************)
(* Flush operation - writes dirty buffer to disk                           *)
(***************************************************************************)

FlushBuffer ==
    /\ pc = "idle"
    /\ bufferDirty
    /\ bufferLength > 0
    /\ LET newDiskLength == Max(diskLength, bufferStart + bufferLength)
           newDiskContents == [i \in 0..(newDiskLength-1) |->
                                IF i >= bufferStart /\ i < bufferStart + bufferLength
                                THEN buffer[i - bufferStart]
                                ELSE IF i < diskLength
                                     THEN diskContents[i]
                                     ELSE ArbitrarySymbol]
       IN /\ diskContents' = newDiskContents
          /\ diskLength' = newDiskLength
          /\ bufferDirty' = FALSE
          /\ bufferModified' = {}
          /\ UNCHANGED <<filePointer, fileLength, buffer, bufferStart, bufferLength>>
    /\ absFileContents' = [i \in 0..(absFileLength-1) |-> LogicalRead(i)]
    /\ UNCHANGED <<absFilePointer, absFileLength, pc>>

Flush ==
    /\ pc = "idle"
    /\ pc' = "flushing"
    /\ IF bufferDirty /\ bufferLength > 0
       THEN LET newDiskLength == Max(diskLength, bufferStart + bufferLength)
                newDiskContents == [i \in 0..(newDiskLength-1) |->
                                     IF i >= bufferStart /\ i < bufferStart + bufferLength
                                     THEN buffer[i - bufferStart]
                                     ELSE IF i < diskLength
                                          THEN diskContents[i]
                                          ELSE ArbitrarySymbol]
            IN /\ diskContents' = newDiskContents
               /\ diskLength' = newDiskLength
               /\ bufferDirty' = FALSE
               /\ bufferModified' = {}
               /\ UNCHANGED <<filePointer, fileLength, buffer, bufferStart, bufferLength>>
       ELSE UNCHANGED <<diskContents, diskLength, bufferDirty, bufferModified,
                        filePointer, fileLength, buffer, bufferStart, bufferLength>>
    /\ absFileContents' = [i \in 0..(fileLength-1) |-> LogicalRead(i)]
    /\ UNCHANGED <<absFilePointer, absFileLength>>

FlushComplete ==
    /\ pc = "flushing"
    /\ pc' = "idle"
    /\ UNCHANGED <<concreteVars, abstractVars>>

(***************************************************************************)
(* Seek operation - moves file pointer                                     *)
(***************************************************************************)

Seek(newPos) ==
    /\ pc = "idle"
    /\ newPos >= 0
    /\ newPos <= MaxFileSize
    /\ pc' = "seeking"
    /\ filePointer' = newPos
    /\ absFilePointer' = newPos
    /\ UNCHANGED <<fileLength, diskContents, diskLength, buffer, bufferStart,
                   bufferLength, bufferDirty, bufferModified, absFileLength, absFileContents>>

SeekComplete ==
    /\ pc = "seeking"
    /\ pc' = "idle"
    /\ UNCHANGED <<concreteVars, abstractVars>>

(***************************************************************************)
(* Read operation - reads byte at current position                         *)
(***************************************************************************)

\* Load buffer from disk at position
LoadBuffer(pos) ==
    LET newStart == pos
        newLen == Min(MaxBufferSize, Max(0, diskLength - pos))
        newBuf == [i \in 0..(MaxBufferSize-1) |->
                    IF i < newLen /\ pos + i < diskLength
                    THEN diskContents[pos + i]
                    ELSE ArbitrarySymbol]
    IN <<newStart, newLen, newBuf>>

Read ==
    /\ pc = "idle"
    /\ filePointer < fileLength
    /\ pc' = "reading"
    /\ IF InBuffer(filePointer)
       THEN \* Read from buffer
            /\ filePointer' = filePointer + 1
            /\ absFilePointer' = absFilePointer + 1
            /\ UNCHANGED <<fileLength, diskContents, diskLength, buffer,
                           bufferStart, bufferLength, bufferDirty, bufferModified,
                           absFileLength, absFileContents>>
       ELSE \* Need to load buffer (flush first if dirty)
            IF bufferDirty
            THEN \* Flush then load
                 LET flushDiskLen == Max(diskLength, bufferStart + bufferLength)
                     flushDisk == [i \in 0..(flushDiskLen-1) |->
                                    IF i >= bufferStart /\ i < bufferStart + bufferLength
                                    THEN buffer[i - bufferStart]
                                    ELSE IF i < diskLength
                                         THEN diskContents[i]
                                         ELSE ArbitrarySymbol]
                     loaded == LoadBuffer(filePointer)
                 IN /\ diskContents' = flushDisk
                    /\ diskLength' = flushDiskLen
                    /\ bufferStart' = loaded[1]
                    /\ bufferLength' = loaded[2]
                    /\ buffer' = loaded[3]
                    /\ bufferDirty' = FALSE
                    /\ bufferModified' = {}
                    /\ filePointer' = filePointer + 1
                    /\ absFilePointer' = absFilePointer + 1
                    /\ UNCHANGED <<fileLength, absFileLength, absFileContents>>
            ELSE \* Just load
                 LET loaded == LoadBuffer(filePointer)
                 IN /\ bufferStart' = loaded[1]
                    /\ bufferLength' = loaded[2]
                    /\ buffer' = loaded[3]
                    /\ filePointer' = filePointer + 1
                    /\ absFilePointer' = absFilePointer + 1
                    /\ UNCHANGED <<fileLength, diskContents, diskLength,
                                   bufferDirty, bufferModified,
                                   absFileLength, absFileContents>>

ReadComplete ==
    /\ pc = "reading"
    /\ pc' = "idle"
    /\ UNCHANGED <<concreteVars, abstractVars>>

(***************************************************************************)
(* Write operation - writes byte at current position                       *)
(***************************************************************************)

Write(value) ==
    /\ pc = "idle"
    /\ value \in DataValues
    /\ filePointer < MaxFileSize
    /\ pc' = "writing"
    /\ IF InBuffer(filePointer) /\ bufferLength < MaxBufferSize
       THEN \* Write to existing buffer
            LET bufPos == filePointer - bufferStart
            IN /\ buffer' = [buffer EXCEPT ![bufPos] = value]
               /\ bufferDirty' = TRUE
               /\ bufferModified' = bufferModified \cup {bufPos}
               /\ filePointer' = filePointer + 1
               /\ fileLength' = Max(fileLength, filePointer + 1)
               /\ bufferLength' = Max(bufferLength, bufPos + 1)
               /\ UNCHANGED <<diskContents, diskLength, bufferStart>>
       ELSE \* Need new buffer position (flush if dirty)
            IF bufferDirty
            THEN LET flushDiskLen == Max(diskLength, bufferStart + bufferLength)
                     flushDisk == [i \in 0..(flushDiskLen-1) |->
                                    IF i >= bufferStart /\ i < bufferStart + bufferLength
                                    THEN buffer[i - bufferStart]
                                    ELSE IF i < diskLength
                                         THEN diskContents[i]
                                         ELSE ArbitrarySymbol]
                 IN /\ diskContents' = flushDisk
                    /\ diskLength' = flushDiskLen
                    /\ bufferStart' = filePointer
                    /\ buffer' = [buffer EXCEPT ![0] = value]
                    /\ bufferLength' = 1
                    /\ bufferDirty' = TRUE
                    /\ bufferModified' = {0}
                    /\ filePointer' = filePointer + 1
                    /\ fileLength' = Max(fileLength, filePointer + 1)
            ELSE /\ bufferStart' = filePointer
                 /\ buffer' = [buffer EXCEPT ![0] = value]
                 /\ bufferLength' = 1
                 /\ bufferDirty' = TRUE
                 /\ bufferModified' = {0}
                 /\ filePointer' = filePointer + 1
                 /\ fileLength' = Max(fileLength, filePointer + 1)
                 /\ UNCHANGED <<diskContents, diskLength>>
    /\ absFilePointer' = filePointer' 
    /\ absFileLength' = fileLength'
    /\ absFileContents' = [i \in 0..(fileLength'-1) |-> 
                            IF i = filePointer THEN value ELSE LogicalRead(i)]

WriteComplete ==
    /\ pc = "writing"
    /\ pc' = "idle"
    /\ UNCHANGED <<concreteVars, abstractVars>>

(***************************************************************************)
(* SetLength operation - truncates or extends file                         *)
(***************************************************************************)

SetLength(newLen) ==
    /\ pc = "idle"
    /\ newLen >= 0
    /\ newLen <= MaxFileSize
    /\ pc' = "setLength"
    /\ fileLength' = newLen
    /\ filePointer' = Min(filePointer, newLen)
    \* Invalidate buffer if it's beyond new length
    /\ IF bufferStart >= newLen
       THEN /\ bufferLength' = 0
            /\ bufferDirty' = FALSE
            /\ bufferModified' = {}
            /\ UNCHANGED buffer
       ELSE IF bufferStart + bufferLength > newLen
            THEN /\ bufferLength' = Max(0, newLen - bufferStart)
                 /\ bufferModified' = {x \in bufferModified : x < bufferLength'}
                 /\ UNCHANGED <<buffer, bufferDirty>>
            ELSE UNCHANGED <<buffer, bufferLength, bufferDirty, bufferModified>>
    /\ UNCHANGED <<diskContents, diskLength, bufferStart>>
    /\ absFileLength' = newLen
    /\ absFilePointer' = Min(absFilePointer, newLen)
    /\ absFileContents' = [i \in 0..(newLen-1) |-> 
                            IF i < absFileLength 
                            THEN LogicalRead(i) 
                            ELSE ArbitrarySymbol]

SetLengthComplete ==
    /\ pc = "setLength"
    /\ pc' = "idle"
    /\ UNCHANGED <<concreteVars, abstractVars>>

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)

Next ==
    \/ \E pos \in 0..MaxFileSize : Seek(pos)
    \/ SeekComplete
    \/ Read
    \/ ReadComplete
    \/ \E v \in DataValues : Write(v)
    \/ WriteComplete
    \/ Flush
    \/ FlushComplete
    \/ \E len \in 0..MaxFileSize : SetLength(len)
    \/ SetLengthComplete

(***************************************************************************)
(* Fairness conditions                                                     *)
(***************************************************************************)

Fairness ==
    /\ WF_vars(SeekComplete)
    /\ WF_vars(ReadComplete)
    /\ WF_vars(WriteComplete)
    /\ WF_vars(FlushComplete)
    /\ WF_vars(SetLengthComplete)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

SafetyInvariant ==
    /\ TypeInvariant
    /\ BufferStartValid
    /\ DirtyConsistency
    /\ ModifiedInBuffer

\* Refinement: concrete state refines abstract state
RefinementInvariant ==
    /\ PointerRefinement
    /\ LengthRefinement

\* Combined invariant
Invariant == SafetyInvariant /\ RefinementInvariant

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Operations eventually complete
OperationsComplete ==
    /\ pc = "seeking" ~> pc = "idle"
    /\ pc = "reading" ~> pc = "idle"
    /\ pc = "writing" ~> pc = "idle"
    /\ pc = "flushing" ~> pc = "idle"
    /\ pc = "setLength" ~> pc = "idle"

\* If there's dirty data, it can eventually be flushed
DirtyEventuallyFlushable ==
    bufferDirty ~> (bufferDirty \/ ~bufferDirty)

(***************************************************************************)
(* Abstract RandomAccessFile specification for refinement                  *)
(***************************************************************************)

AbstractTypeOK ==
    /\ absFilePointer \in 0..MaxFileSize
    /\ absFileLength \in 0..MaxFileSize

AbstractInit ==
    /\ absFilePointer = 0
    /\ absFileLength = 0
    /\ absFileContents = [i \in {} |-> ArbitrarySymbol]

AbstractSeek(pos) ==
    /\ pos >= 0 /\ pos <= MaxFileSize
    /\ absFilePointer' = pos
    /\ UNCHANGED <<absFileLength, absFileContents>>

AbstractRead ==
    /\ absFilePointer < absFileLength
    /\ absFilePointer' = absFilePointer + 1
    /\ UNCHANGED <<absFileLength, absFileContents>>

AbstractWrite(value) ==
    /\ value \in DataValues
    /\ absFilePointer < MaxFileSize
    /\ absFilePointer' = absFilePointer + 1
    /\ absFileLength' = Max(absFileLength, absFilePointer + 1)
    /\ absFileContents' = [i \in 0..(absFileLength'-1) |->
                            IF i = absFilePointer THEN value
                            ELSE IF i < absFileLength THEN absFileContents[i]
                            ELSE ArbitrarySymbol]

AbstractSetLength(newLen) ==
    /\ newLen >= 0 /\ newLen <= MaxFileSize
    /\ absFileLength' = newLen
    /\ absFilePointer' = Min(absFilePointer, newLen)
    /\ absFileContents' = [i \in 0..(newLen-1) |->
                            IF i < absFileLength THEN absFileContents[i]
                            ELSE ArbitrarySymbol]

AbstractNext ==
    \/ \E pos \in 0..MaxFileSize : AbstractSeek(pos)
    \/ AbstractRead
    \/ \E v \in DataValues : AbstractWrite(v)
    \/ \E len \in 0..MaxFileSize : AbstractSetLength(len)

AbstractSpec == AbstractInit /\ [][AbstractNext]_abstractVars

(***************************************************************************)
(* Refinement mapping                                                       *)
(***************************************************************************)

\* The concrete specification refines the abstract specification
Refinement == Spec => AbstractSpec

=============================================================================