-------------------- MODULE hvc -------------------
EXTENDS Integers
CONSTANT N, STOP, EPS
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

(* Hybrid Logical Clocks algorithm
--algorithm hvc {
  variable pt = [j \in Procs |-> 0], msg= [j \in Procs |-> [k \in Procs |-> 0]]; \* shared/aux var
  fair process (j \in Procs)
  variable vc = [j \in Procs |-> 0];
  {J0:while (pt[self] < STOP)
      {either 
       Recv:{ \* local or receive event
         \* if not heard increase msg[self][not heard]= msg[self][not heard] + EPS
            await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
             with(k \in Procs \ {self}){
                if(msg[self][k] < pt[self] + EPS){
                    msg[self][k] := msg[self][k] + EPS ;
                }
            };
            vc[self] := SetMax({pt[self],vc[self],msg[self][self]});
        } 
       or
       Send:{ \* send event
         await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
            if (vc[self]<pt[self])vc[self]:=pt[self];
            with(k \in Procs \ {self}){ msg[k][self] := vc[self] };
        }    
      } 
  }
}

*)
\* BEGIN TRANSLATION
VARIABLES pt, msg, pc, vc

vars == << pt, msg, pc, vc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |-> [k \in Procs |-> 0]]
        (* Process j *)
        /\ vc = [self \in Procs |-> [j \in Procs |-> 0]]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Recv"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, vc >>

Recv(self) == /\ pc[self] = "Recv"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ \E k \in Procs \ {self}:
                   IF msg[self][k] < pt'[self] + EPS
                      THEN /\ msg' = [msg EXCEPT ![self][k] = msg[self][k] + EPS]
                      ELSE /\ TRUE
                           /\ msg' = msg
              /\ vc' = [vc EXCEPT ![self][self] = SetMax({pt'[self],vc[self][self],msg'[self][self]})]
              /\ pc' = [pc EXCEPT ![self] = "J0"]

Send(self) == /\ pc[self] = "Send"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ IF vc[self][self]<pt'[self]
                    THEN /\ vc' = [vc EXCEPT ![self][self] = pt'[self]]
                    ELSE /\ TRUE
                         /\ vc' = vc
              /\ \E k \in Procs \ {self}:
                   msg' = [msg EXCEPT ![k][self] = vc'[self][self]]
              /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ Recv(self) \/ Send(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

TypeOK == (\A k \in Procs : vc[k][k] >= pt[k] /\ vc[k][k] <= pt[k]+EPS)
\* END TRANSLATION
==================================================
