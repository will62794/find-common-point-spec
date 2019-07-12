---------------------------------------- MODULE CommonPoint ----------------------------------------
EXTENDS Integers, Naturals, Sequences

\*
\* Find the rollback common point.
\*

CONSTANT Nil

\* The logs of each node, local (rollback node) and remote (sync source).
VARIABLE localLog
VARIABLE remoteLog

\* The current log entry index we're pointing at in either local or remote log.
VARIABLE localLogIndex
VARIABLE remoteLogIndex

\* The value of the common point, after it's been found.
VARIABLE commonPoint

StepBackInLocalLog == 
    /\ localLog[localLogIndex].ts > remoteLog[remoteLogIndex].ts
    /\ localLogIndex' = localLogIndex - 1
    /\ UNCHANGED <<localLog, remoteLog, remoteLogIndex, commonPoint>>

StepBackInRemoteLog ==
    /\ remoteLog[remoteLogIndex].ts > localLog[localLogIndex].ts
    /\ remoteLogIndex' = remoteLogIndex - 1
    /\ UNCHANGED <<localLog, remoteLog, localLogIndex, commonPoint>>

StepBackInEitherLog == 
    \* If timestamps of current entries in both logs are equal, then it's possible
    \* we've found the common point. It's also possible, though, that we just happened
    \* to run into two identical timestamps with differing terms. In reality, we would 
    \* need to have a term value to know whether this is really the common point or not. 
    \* For the sake of this simple spec, though, we just assume that all entries past the 
    \* common point in each logs have different terms, so if we find two identical timestamps 
    \* past the common point, then we assume it's not a real common point and step back in either one 
    \* of the logs.
    /\ localLog[localLogIndex].ts = remoteLog[remoteLogIndex].ts
    /\ localLog[localLogIndex].term # remoteLog[remoteLogIndex].term
    \* Step back in either log. We could pick an aribtrary log, but this makes the spec more general.
    /\ \/ (/\ remoteLogIndex' = remoteLogIndex - 1
           /\ UNCHANGED <<localLog, remoteLog, localLogIndex, commonPoint>>)
       \/ (/\ localLogIndex' = localLogIndex - 1
           /\ UNCHANGED <<localLog, remoteLog, remoteLogIndex, commonPoint>>)

FindCommonPoint == 
    \* Timestamp and terms are equal.
    /\ localLog[localLogIndex] = remoteLog[remoteLogIndex]
    /\ commonPoint' = localLog[localLogIndex]
    /\ UNCHANGED <<localLog, remoteLog, localLogIndex, remoteLogIndex>>
 
 
\*
\* Define initial states.
\*  

MaxLogLength == 3
Timestamps == 1..6 \* the set of all possible timestamps.

\* The set of all timestamp sequences. 
TimestampSeq == [1..MaxLogLength -> Timestamps]

\* The set of all timestamp sequences that are monotonically increasing. 
TimestampSeqMonotonic == {l \in TimestampSeq : \A i \in DOMAIN l : (i > 1) => l[i-1] < l[i]}

\* Is log x a prefix of log y?
IsPrefix(x, y) == (Len(x) <= Len(y)) => \A i \in DOMAIN x : x[i] = y[i]
   
Init == 
    \* Each log starts with some common prefix and some arbitrary divergent suffix. The common
    \* point entry has the same term in both logs, and the suffixes have differing terms. This would
    \* be the case in a real rollback scenario.
    LET commonPrefix == <<[ts |-> 0, term |-> 0]>>
        localTerm == 1
        remoteTerm == 2 IN
    /\ \E L, R \in TimestampSeqMonotonic : 
         /\ ~IsPrefix(L, R) /\ ~IsPrefix(R, L)
         /\ localLog  = commonPrefix \o [i \in DOMAIN L |-> [ts |-> L[i], term |-> localTerm]]
         /\ localLogIndex = Len(L) + 1
         /\ remoteLog = commonPrefix \o [i \in DOMAIN R |-> [ts |-> R[i], term |-> remoteTerm]]
         /\ remoteLogIndex = Len(R) + 1 
    /\ commonPoint = Nil

Next == 
    \/ StepBackInLocalLog
    \/ StepBackInRemoteLog
    \/ StepBackInEitherLog
    \/ FindCommonPoint

\* If we've found a common point, it should be the correct one.
CommonPointCorrect == (commonPoint # Nil) => commonPoint = [ts |-> 0, term |-> 0]

\* Make sure we're never in a state where we could step backwards behind the beginning of our log.
NeverStepBackwardsOffLog == 
    /\ ENABLED StepBackInLocalLog => localLogIndex > 1
    /\ ENABLED StepBackInRemoteLog => remoteLogIndex > 1
    /\ ENABLED StepBackInEitherLog => localLogIndex > 1 /\ remoteLogIndex > 1


\* If there is a timestamp T that appears in both logs, then it is true that there must be a state
\* in the behavior where both log pointers are pointing to this timestamp in their respective logs.
\* 
\*  e.g. Index:        1 2 3 4 5
\*       Local Log  : [0 1 2 5 7]
\*       Remote Log : [0 2 3 4 5]
\*
\*      For these particular logs, the algorithm's behaviors must include states that have:
\*      [localLogIndex = 4, remoteLogIndex = 5] (timestamp 5)
\*      [localLogIndex = 3, remoteLogIndex = 2] (timestamp 2)
\*     
\* I believe this property can be used to prove that the common point is always found, since the common point
\* timestamp is always shared between both logs, so we would never "miss" it.       
LogPointersAlignAtCommonTimestamp == 
    \E i, j \in 1..(MaxLogLength + 1) : 
    localLog[i].ts = remoteLog[j].ts => 
        <> (/\ localLogIndex = i 
            /\ remoteLogIndex = j)
            
====================================================================================================
\* Modification History
\* Last modified Fri Jul 12 13:24:54 EDT 2019 by williamschultz
\* Created Tue Jul 09 13:04:07 EDT 2019 by williamschultz
