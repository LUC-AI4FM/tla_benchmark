------------------------------- MODULE BufferedRandomAccessFile -------------------------------

CONSTANTS MaxOffset, BuffSz

VARIABLES file, buffer, bufStart, bufLen, curPos, dirty

(* --algorithm BufferedRandomAccessFile

variables 
    file = <<>>,          \* The underlying file content as a sequence of bytes
    buffer = <<>>,        \* The in-memory buffer
    bufStart = 0,         \* Starting offset of the buffer in the file
    bufLen = 0,           \* Length of valid data in the buffer
    curPos = 0,           \* Current position in the file
    dirty = FALSE;       \* Whether the buffer contains unsaved changes

\* TypeOK: Ensures all variables are of the correct type
TypeOK == /\ file \in Seq(Nat)
          /\ buffer \in Seq(Nat) 
          /\ bufStart \in 0..MaxOffset
          /\ bufLen \in 0..BuffSz
          /\ curPos \in 0..MaxOffset
          /\ dirty \in BOOLEAN

\* Inv1: Buffer bounds invariant
Inv1 == /\ curPos \geq bufStart
        /\ curPos \leq bufStart + bufLen

\* Inv2CanAlwaysBeRestored: It must always be possible to restore the buffer bounds invariant by flushing (if dirty) and then seeking to the current position.
Inv2CanAlwaysBeRestored == \/ ~dirty 
                           \/ /\ dirty
                              /\ curPos \geq 0
                              /\ curPos \leq MaxOffset

\* Inv3: Buffer coherence
Inv3 == \A i \in 0..bufLen-1 : file[bufStart + i] = buffer[i]

\* Inv4: Unbuffered region coherence
Inv4 == \A i \notin bufStart..(bufStart+bufLen-1) : i < Len(file) => file[i] = file[i]

\* Inv5: Dirty tracking correctness
Inv5 == \/ ~dirty 
        \/ /\ dirty
           /\ \E i \in 0..bufLen-1 : buffer[i] # file[bufStart + i]

\* Safety: Combines all invariants
Safety == TypeOK /\ Inv1 /\ Inv2CanAlwaysBeRestored /\ Inv3 /\ Inv4 /\ Inv5

\* FlushBufferCorrect: Flushing must be enabled whenever the buffer is dirty, and it must clear the dirty flag.
FlushBufferCorrect ==
    \E newFile :
        /\ dirty
        /\ newFile = [file EXCEPT ![bufStart..(bufStart+bufLen-1)] = buffer]
        /\ \/ <<newFile, buffer, bufStart, bufLen, curPos, FALSE>> \in [][Next]_<<file, buffer, bufStart, bufLen, curPos, dirty>>

\* SeekCorrect: Seeking to any valid offset must be possible and should not change the file content.
SeekCorrect ==
    \A newPos \in 0..MaxOffset :
        \/ <<file, buffer, newPos, bufLen, newPos, dirty>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>

\* SeekEstablishesInv2: Seeking to the current position must be enabled when not dirty and it must restore the buffer bounds invariant.
SeekEstablishesInv2 ==
    \/ ~dirty
       /\ <<file, buffer, curPos, bufLen, curPos, FALSE>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>

\* Write1Correct: Writing a single byte at the current position must be possible and should update the file content and buffer accordingly.
Write1Correct ==
    \A b \in Nat :
        \/ /\ curPos < MaxOffset
           /\ <<file[0..curPos-1] @@ <<b>> @@ file[curPos+1..Len(file)-1], 
               [buffer EXCEPT ![curPos-bufStart] = b], 
               curPos + 1, bufLen, curPos + 1, TRUE>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>
        \/ /\ curPos = MaxOffset
           /\ <<file @@ <<b>>, 
               [buffer EXCEPT ![curPos-bufStart] = b], 
               curPos + 1, bufLen, curPos + 1, TRUE>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>

\* Read1Correct: Reading a single byte at the current position must be possible and should not change the file content.
Read1Correct ==
    \/ /\ curPos < Len(file)
       /\ <<file, buffer, curPos + 1, bufLen, curPos + 1, dirty>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>
    \/ /\ curPos = Len(file)
       /\ <<file, buffer, curPos, bufLen, curPos, dirty>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>

\* WriteAtMostCorrect: Writing up to BuffSz bytes at the current position must be possible and should update the file content and buffer accordingly.
WriteAtMostCorrect ==
    \A data \in Seq(Nat) :
        /\ Len(data) <= BuffSz
        /\ \/ /\ curPos + Len(data) <= MaxOffset
               /\ <<file[0..curPos-1] @@ data @@ file[curPos+Len(data)..Len(file)-1], 
                   [buffer EXCEPT ![curPos-bufStart..(curPos-bufStart)+Len(data)-1] = data], 
                   curPos + Len(data), bufLen, curPos + Len(data), TRUE>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>
           \/ /\ curPos + Len(data) > MaxOffset
              /\ <<file @@ data[0..MaxOffset-curPos-1], 
                  [buffer EXCEPT ![curPos-bufStart..(curPos-bufStart)+Len(data)-1] = data[0..MaxOffset-curPos-1]], 
                  curPos + Len(data), bufLen, curPos + Len(data), TRUE>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>

\* ReadCorrect: Reading up to BuffSz bytes at the current position must be possible and should not change the file content.
ReadCorrect ==
    \/ /\ curPos < Len(file)
       /\ <<file, buffer, curPos + Min(bufLen - (curPos - bufStart), BuffSz), bufLen, curPos + Min(bufLen - (curPos - bufStart), BuffSz), dirty>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>
    \/ /\ curPos = Len(file)
       /\ <<file, buffer, curPos, bufLen, curPos, dirty>> \in [][Next]_<<file, buffer, curPos, bufLen, curPos, dirty>>

\* Next: Defines the possible state transitions
Next ==
    \/ FlushBufferCorrect
    \/ SeekCorrect
    \/ Write1Correct
    \/ Read1Correct
    \/ WriteAtMostCorrect
    \/ ReadCorrect

Spec == /\ TypeOK
        /\ WF_<<file, buffer, bufStart, bufLen, curPos, dirty>>[Next]
        /\ \A s \in Init : Safety[s]

Init ==
    /\ file = <<>>
    /\ buffer = <<>>
    /\ bufStart = 0
    /\ bufLen = 0
    /\ curPos = 0
    /\ dirty = FALSE

Symbols == {"file", "buffer", "bufStart", "bufLen", "curPos", "dirty"}

ArbitrarySymbol == CHOOSE s \in Symbols : TRUE

end algorithm *)

=============================================================================