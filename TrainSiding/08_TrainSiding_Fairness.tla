The previous model showed problems with stuttering. Our trains could get stuck in front of a semaphore and not 
choose to move even though the movement was enabled.
This is solved by adding the property of "Fairness" to all actions - which means when they are allowed, they will eventually happen.

There is another stuttering step if we just leave the spec like this - one where the systems loops between changing the 
semaphore states and the switch states without moving the trains.
This is fixed by only changing the switches when a train movement needs the switch.

The next problem this improved model finds is a deadlock. The error trace reveals that it happens once train 1 is on track 4
and train 2 is on track 1 - so both trains have safely passed each other. Success, finally!

Why does TLC report a deadlock here? It is because we have only specified the system up to this point.
When we disable the check for deadlocks, the model checker finds another possible situation for stuttering steps.
What does this mean?
---------------------------- MODULE 08_TrainSiding_Fairness----------------------------
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
                /\ s1' = "STOP" \* Change semaphore to STOP once the train has passed it
                /\ UNCHANGED s2   
             \/ /\ t1 = "SWITCH1"
                /\ t1' = "TRACK2"
                /\ UNCHANGED <<s1, s2>>
             \/ /\ t1 = "TRACK2"
                /\ s2 = "GO"
                /\ t1' = "SWITCH2"
                /\ UNCHANGED <<s1>>
                /\ s2' = "STOP"
             \/ /\ t1 = "SWITCH2"
                /\ t1' = "TRACK4"
                /\ UNCHANGED <<s1, s2>>
          /\ UNCHANGED <<t2, s3, s4, sw1, sw2>>
          
\* Move Train 2 via the siding 
MoveT2 == /\ \/ /\ t2 = "TRACK4"
                /\ s4 = "GO"
                /\ t2' = "SWITCH2"
                /\ UNCHANGED s3
                /\ s4' = "STOP"
             \/ /\ t2 = "SWITCH2"
                /\ t2' = IF sw2 = "STRAIGHT" THEN "TRACK2" ELSE "TRACK3"
                /\ UNCHANGED <<s3, s4>>
             \/ /\ t2 = "TRACK3"
                /\ s3 = "GO"
                /\ t2' = "SWITCH1"
                /\ s3' = "STOP"
                /\ UNCHANGED s4
             \/ /\ t2 = "SWITCH1"
                /\ t2' = "TRACK1"
                /\ UNCHANGED <<s3, s4>>
          /\ UNCHANGED <<t1, s1, s2, sw1, sw2>>
       
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

\* Change one of the switches           
ChangeSw1 == /\ s1 = "STOP"
             /\ s3 = "STOP"
             /\ t1 /= "SWITCH1"
             /\ t2 /= "SWITCH1"
             /\ \/ /\ sw1 = "STRAIGHT"
                   /\ t2 = "TRACK3"
                   /\ sw1' = "LEFT"
                \/ /\ sw1 = "LEFT"
                   /\ t1 = "TRACK1"
                   /\ sw1' = "STRAIGHT"
             /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw2>>
             
ChangeSw2 == /\ s2 = "STOP"
             /\ s4 = "STOP" 
             /\ t1 /= "SWITCH2"
             /\ t2 /= "SWITCH2"
             /\ \/ /\ sw2 = "STRAIGHT"
                   /\ t2 = "TRACK4"
                   /\ sw2' = "RIGHT"
                \/ /\ sw2 = "RIGHT"
                   /\ t1 = "TRACK2"
                   /\ sw2' = "STRAIGHT"
             /\ UNCHANGED <<t1, t2, s1, s2, s3, s4, sw1>>
                    
------------------------------------------------------------------------------
\* Specification        
Next == MoveT1 \/ MoveT2 \/ ChangeS1 \/ ChangeS2 \/ ChangeS3 \/ ChangeS4 \/ ChangeSw1 \/ ChangeSw2
Spec == Init /\ [][Next]_vars 
        /\ WF_vars(MoveT1) 
        /\ WF_vars(MoveT2) 
        /\ WF_vars(ChangeS1) 
        /\ WF_vars(ChangeS2) 
        /\ WF_vars(ChangeS3) 
        /\ WF_vars(ChangeS4) 
        /\ WF_vars(ChangeSw1) 
        /\ WF_vars(ChangeSw2)
=============================================================================