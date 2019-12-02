An improved model of the train siding.
The trains both move in a straight line, but they will obey the semaphores. 
No they will not collide any more, but they get stuck, which is detected as a deadlock by the model checker.
---------------------------- MODULE 02_TrainSiding_Semaphores ----------------------------
VARIABLES t1, t2, s1, s2, s3, s4, sw1, sw2

vars == <<t1, t2, s1, s2, s3, s4, sw1, sw2>>

Init == /\ t1 = "TRACK1"    \* Position of Train 1  
        /\ t2 = "TRACK4"    \* Position of Train 2
        /\ s1 = "STOP"      \* Signal of Semaphore 1
        /\ s2 = "STOP"      \* Signal of Semaphore 2
        /\ s3 = "STOP"      \* Signal of Semaphore 3
        /\ s4 = "STOP"      \* Signal of Semaphore 4
        /\ sw1 = "STRAIGHT" \* Direction of Switch 1
        /\ sw2 = "STRAIGHT" \* Direction of Switch 2
------------------------------------------------------------------------------
\* Type Invariants that check for programming mistakes
Positions == {"TRACK1", "TRACK2", "TRACK3", "TRACK4", "SWITCH1", "SWITCH2"}
Signals == {"STOP", "GO"}        
TypeInvariants == /\ t1 \in Positions
                  /\ t2 \in Positions
                  /\ s1 \in Signals
                  /\ s2 \in Signals
                  /\ s3 \in Signals
                  /\ s4 \in Signals
                  /\ sw1 \in {"STRAIGHT", "LEFT"}
                  /\ sw2 \in {"STRAIGHT", "RIGHT"}              
   
\* Safety Properties (a.k.a Invariants) that check that both Trains will be unharmed
NoCollisions ==  t1 /= t2

\* Properties: Specification of the eventual outcome (both trains have crossed the siding)
Train1Crossed == t1 = "TRACK4"
Train2Crossed == t2 = "TRACK1"
CrossingSuccessful == <>Train1Crossed /\ <>Train2Crossed      

------------------------------------------------------------------------------
\* Actions
\* Move Train 1 in a straight Line
MoveT1 == /\ \/ /\ t1 = "TRACK1"
                /\ s1 = "GO"
                /\ t1' = "SWITCH1"
             \/ /\ t1 = "SWITCH1"
                /\ t1' = "TRACK2"
             \/ /\ t1 = "TRACK2"
                /\ s2 = "GO"
                /\ t1' = "SWITCH2"
             \/ /\ t1 = "SWITCH2"
                /\ t1' = "TRACK4"
          /\ UNCHANGED <<t2, s1, s2, s3, s4, sw1, sw2>>
          
\* Move Train 2 in a straight Line     
MoveT2 == /\ \/ /\ t2 = "TRACK4"
                /\ s4 = "GO"
                /\ t2' = "SWITCH2"
             \/ /\ t2 = "SWITCH2"
                /\ t2' = "TRACK2"
             \/ /\ t2 = "TRACK2"
                /\ t2' = "SWITCH1"
             \/ /\ t2 = "SWITCH1"
                /\ t2' = "TRACK1"
          /\ UNCHANGED <<t1, s1, s2, s3, s4, sw1, sw2>>
          
------------------------------------------------------------------------------
\* Specification        
Next == MoveT1 \/ MoveT2
Spec == Init /\ [][Next]_vars
=============================================================================