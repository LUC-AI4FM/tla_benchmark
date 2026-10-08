------------------------------- MODULE BufferedFile -------------------------------

CONSTANTS MaxOffset, BuffSz

VARIABLES fileImage, buffer, bufStart, bufEnd, dirty, logicalLength, pointer

(*--algorithm BufferedFile
variables 
    fileImage = <<>>,          \* Underlying file contents
    buffer = <<>>,              \* In-memory buffer
    bufStart = 0,               \* Start offset of the buffer window in the file
    bufEnd = 0,                 \* End offset of the buffer window in the file (exclusive)
    dirty = FALSE,              \* Flag indicating if the buffer has unsaved changes
    logicalLength = 0,          \* Logical length of the file
    pointer = 0;                \* Current position of the file pointer

\* TypeOK: Ensures all variables are of correct types
TypeOK == 
    /\ fileImage \in Seq(Nat)
    /\ buffer \in Seq(Nat) 
    /\ bufStart \in Nat
    /\ bufEnd \in Nat
    /\ dirty \in BOOLEAN
    /\ logicalLength \in Nat
    /\ pointer \in 0..MaxOffset

\* Inv1: Buffer window bounds are consistent with the buffer size and file length
Inv1 == 
    /\ bufStart <= bufEnd
    /\ bufEnd - bufStart = Len(buffer)
    /\ bufEnd <= logicalLength + BuffSz

\* Inv2CanAlwaysBeRestored: If dirty, there exists a sequence of actions that can flush and refill the buffer
Inv2CanAlwaysBeRestored == 
    \/ ~dirty
    \/ \E newFileImage \in Seq(Nat) : FlushBuffer(fileImage, buffer, bufStart, logicalLength) = newFileImage

\* Inv3: Buffer contents are consistent with fileImage within the window bounds
Inv3 ==
    /\ Len(buffer) <= BuffSz
    /\ \A i \in 0..Len(buffer)-1 : 
        \/ bufStart + i >= logicalLength
        \/ buffer[i] = fileImage[bufStart + i]

\* Inv4: Pointer is within the logical length of the file
Inv4 ==
    pointer \in 0..logicalLength

\* Inv5: Buffer end does not exceed MaxOffset
Inv5 ==
    bufEnd <= MaxOffset

\* Safety: All invariants hold
Safety == 
    /\ TypeOK
    /\ Inv1
    /\ Inv3
    /\ Inv4
    /\ Inv5

\* FlushBufferCorrect: Flushing the buffer updates fileImage and clears dirty flag
FlushBuffer ==
    IF dirty THEN
        LET newFileImage == [fileImage EXCEPT ![bufStart..bufEnd-1] = buffer]
        IN  <<newFileImage, FALSE>>
    ELSE
        <<fileImage, FALSE>>

\* SeekCorrect: Seeking to a position updates the pointer and may refill the buffer
Seek(newPointer) ==
    IF newPointer \in bufStart..bufEnd-1 THEN
        /\ pointer' = newPointer
        /\ UNCHANGED <<fileImage, buffer, bufStart, bufEnd, dirty, logicalLength>>
    ELSE
        LET newBufStart == (newPointer \div BuffSz) * BuffSz
            newBufEnd == Min(newBufStart + BuffSz, logicalLength)
            newBuffer == [i \in 0..BuffSz-1 |-> IF newBufStart + i < logicalLength THEN fileImage[newBufStart + i] ELSE 0]
        IN  /\ pointer' = newPointer
            /\ bufStart' = newBufStart
            /\ bufEnd' = newBufEnd
            /\ buffer' = newBuffer
            /\ dirty' = FALSE
            /\ UNCHANGED <<fileImage, logicalLength>>

\* SeekEstablishesInv2: Seeking establishes Inv2CanAlwaysBeRestored
SeekEstablishesInv2 ==
    \A newPointer \in 0..MaxOffset : 
        \/ ~dirty
        \/ \E newFileImage \in Seq(Nat) : FlushBuffer(fileImage, buffer, bufStart, logicalLength) = newFileImage

\* Write1Correct: Writing a single byte updates the buffer and sets dirty flag
Write1(byte) ==
    LET offset == pointer
        newPointer == (offset + 1)
        newBufIndex == offset - bufStart
    IN  IF offset < bufEnd THEN
            /\ buffer' = [buffer EXCEPT ![newBufIndex] = byte]
            /\ dirty' = TRUE
            /\ pointer' = newPointer
            /\ UNCHANGED <<fileImage, bufStart, bufEnd, logicalLength>>
        ELSE
            LET newBufStart == (offset \div BuffSz) * BuffSz
                newBufEnd == Min(newBufStart + BuffSz, logicalLength)
                newBuffer == [i \in 0..BuffSz-1 |-> IF newBufStart + i < logicalLength THEN fileImage[newBufStart + i] ELSE 0]
            IN  /\ buffer' = [newBuffer EXCEPT ![offset - newBufStart] = byte]
                /\ dirty' = TRUE
                /\ pointer' = newPointer
                /\ bufStart' = newBufStart
                /\ bufEnd' = newBufEnd
                /\ UNCHANGED <<fileImage, logicalLength>>

\* Read1Correct: Reading a single byte returns the correct value and updates the pointer
Read1 ==
    LET offset == pointer
        newPointer == (offset + 1)
        newBufIndex == offset - bufStart
    IN  IF offset < bufEnd THEN
            /\ pointer' = newPointer
            /\ UNCHANGED <<fileImage, buffer, bufStart, bufEnd, dirty, logicalLength>>
            /\ RETURN buffer[newBufIndex]
        ELSE
            LET newBufStart == (offset \div BuffSz) * BuffSz
                newBufEnd == Min(newBufStart + BuffSz, logicalLength)
                newBuffer == [i \in 0..BuffSz-1 |-> IF newBufStart + i < logicalLength THEN fileImage[newBufStart + i] ELSE 0]
            IN  /\ pointer' = newPointer
                /\ bufStart' = newBufStart
                /\ bufEnd' = newBufEnd
                /\ buffer' = newBuffer
                /\ dirty' = FALSE
                /\ UNCHANGED <<fileImage, logicalLength>>
                /\ RETURN newBuffer[offset - newBufStart]

\* WriteAtMostCorrect: Writing multiple bytes updates the buffer and sets dirty flag
WriteAtMost(bytes) ==
    LET offset == pointer
        n == Len(bytes)
        newPointer == (offset + n)
        newBufIndices == {i \in 0..n-1 |-> i}
        newFileImage == [fileImage EXCEPT ![offset..newPointer-1] = bytes]
    IN  IF offset < bufEnd THEN
            /\ buffer' = [buffer EXCEPT ![i \in newBufIndices |-> bytes[i]]]
            /\ dirty' = TRUE
            /\ pointer' = newPointer
            /\ UNCHANGED <<fileImage, bufStart, logicalLength>>
        ELSE
            LET newBufStart == (offset \div BuffSz) * BuffSz
                newBufEnd == Min(newBufStart + BuffSz, logicalLength)
                newBuffer == [i \in 0..BuffSz-1 |-> IF newBufStart + i < logicalLength THEN fileImage[newBufStart + i] ELSE 0]
            IN  /\ buffer' = [newBuffer EXCEPT ![i \in newBufIndices |-> bytes[i]]]
                /\ dirty' = TRUE
                /\ pointer' = newPointer
                /\ bufStart' = newBufStart
                /\ bufEnd' = newBufEnd
                /\ UNCHANGED <<fileImage, logicalLength>>

\* ReadCorrect: Reading multiple bytes returns the correct values and updates the pointer
Read(n) ==
    LET offset == pointer
        newPointer == (offset + n)
        newBufIndices == {i \in 0..n-1 |-> i}
    IN  IF offset < bufEnd THEN
            /\ pointer' = newPointer
            /\ UNCHANGED <<fileImage, buffer, bufStart, bufEnd, dirty, logicalLength>>
            /\ RETURN [i \in newBufIndices |-> buffer[offset - bufStart + i]]
        ELSE
            LET newBufStart == (offset \div BuffSz) * BuffSz
                newBufEnd == Min(newBufStart + BuffSz, logicalLength)
                newBuffer == [i \in 0..BuffSz-1 |-> IF newBufStart + i < logicalLength THEN fileImage[newBufStart + i] ELSE 0]
            IN  /\ pointer' = newPointer
                /\ bufStart' = newBufStart
                /\ bufEnd' = newBufEnd
                /\ buffer' = newBuffer
                /\ dirty' = FALSE
                /\ UNCHANGED <<fileImage, logicalLength>>
                /\ RETURN [i \in newBufIndices |-> newBuffer[offset - newBufStart + i]]

\* SetLengthCorrect: Setting the length updates the logical file length and adjusts pointer if necessary
SetLength(newLength) ==
    LET newFileImage == IF newLength > logicalLength THEN 
                            <<fileImage >> [newLogicalLength \in logicalLength..newLength-1 |-> 0]
                        ELSE
                            SubSeq(fileImage, 1, newLength)
        newPointer == Min(pointer, newLength)
    IN  /\ fileImage' = newFileImage
        /\ logicalLength' = newLength
        /\ pointer' = newPointer
        /\ IF newLength < bufEnd THEN
            LET newBufStart == (newPointer \div BuffSz) * BuffSz
                newBufEnd == Min(newBufStart + BuffSz, newLength)
                newBuffer == [i \in 0..BuffSz-1 |-> IF newBufStart + i < newLength THEN fileImage[newBufStart + i] ELSE 0]
            IN  /\ bufStart' = newBufStart
                /\ bufEnd' = newBufEnd
                /\ buffer' = newBuffer
                /\ dirty' = FALSE
        ELSE
            UNCHANGED <<bufStart, bufEnd, buffer, dirty>>

end algorithm *)

Spec == 
    /\ TypeOK
    /\ Inv1
    /\ Inv3
    /\ Inv4
    /\ Inv5

Symbols == {"fileImage", "buffer", "bufStart", "bufEnd", "dirty", "logicalLength", "pointer"}

ArbitrarySymbol == CHOOSE sym \in Symbols : TRUE

=============================================================================