An improved model of the train siding.
This model adds semaphores that can switch their state. Obviously, if they just did that, we would have another collision.
So this model adds changing of one of the switches as well so the trains can avoid each other.
This shows that the deadlock is solved, but now we have the problem that our temporal property "CrossingSuccessful" is violated as 
switch 2 is never changed.
---------------------------- MODULE 03_TrainSiding_ChangingSemaphores ----------------------------
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
       
\* Change one of the semaphores
ChangeS1 == /\ t1 = "TRACK1"
            /\ t2 \notin {"TRACK2", "SWITCH1"}
            /\ sw1 = "STRAIGHT"
            /\ s1' = "GO"
            /\ UNCHANGED <<t1, t2, s2, s3, s4, sw1, sw2>>
            
ChangeS2 == /\ t1 = "TRACK2"
            /\ t2 \notin {"TRACK4", "SWITCH2"}
            /\ sw2 = "STRAIGHT"
            /\ s2' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s3, s4, sw1, sw2>>
            
ChangeS3 == /\ t2 = "TRACK3"
            /\ t1 \notin {"TRACK1", "SWITCH1"}
            /\ sw1 = "LEFT"
            /\ s3' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s2, s4, sw1, sw2>>
            
ChangeS4 == /\ t2 = "TRACK4"
            /\ t1 \notin {"TRACK3", "SWITCH2"}
            /\ sw2 = "RIGHT"
            /\ s4' = "GO"
            /\ UNCHANGED <<t1, t2, s1, s2, s3, sw1, sw2>>
            
\* Change switch 1                     
ChangeSw1 == /\ \/ /\ sw1 = "STRAIGHT"
                   /\ sw1' = "LEFT"
                \/ /\ sw1 = "LEFT"
                   /\ sw1' = "STRAIGHT"
             /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw2>>
                    
------------------------------------------------------------------------------
\* Specification        
Next == MoveT1 \/ MoveT2 \/ ChangeS1 \/ ChangeS2 \/ ChangeS3 \/ ChangeS4 \/ ChangeSw1
Spec == Init /\ [][Next]_vars
=============================================================================