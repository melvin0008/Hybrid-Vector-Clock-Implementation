-------------------- MODULE hvc -------------------
EXTENDS Integers
CONSTANT N, STOP, EPS
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

(* Hybrid Logical Clocks algorithm
--algorithm hvc {
  variable pt = [j \in Procs |-> 0], msg= [j \in Procs |->[k \in Procs |-> 0]]; \* shared/aux vars
  fair process (j \in Procs)
  variables vc = [j \in Procs |-> 0], m=0;
  {J0:while (pt[self] < STOP)
      {either 
       Recv:{ \* local or receive event
            await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
            m := 1;
             J1:while(m  #  N){
                    if( m # self)
                    { vc[m] := SetMax({vc[m],msg[self][m], pt[self] - EPS} ) };
                    m := m+1;
            };
            vc[self] := SetMax({pt[self],vc[self],msg[self][self]+1});
        } 
       or
       Send:{ \* send event
         await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
          if (vc[self]<pt[self]) vc[self]:=pt[self];
          else vc[self] := vc[self]+1;
            with(k \in Procs \ {self})
                { msg[k]:=  vc  };
        }    
      } 
  }
}

*)
\* BEGIN TRANSLATION
VARIABLES pt, msg, pc, vc, m

vars == << pt, msg, pc, vc, m >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ msg = [j \in Procs |->[k \in Procs |-> 0]]
        (* Process j *)
        /\ vc = [self \in Procs |-> [j \in Procs |-> 0]]
        /\ m = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "Recv"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, msg, vc, m >>

Recv(self) == /\ pc[self] = "Recv"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ m' = [m EXCEPT ![self] = 1]
              /\ pc' = [pc EXCEPT ![self] = "J1"]
              /\ UNCHANGED << msg, vc >>

J1(self) == /\ pc[self] = "J1"
            /\ IF m[self]  #  N
                  THEN /\ IF m[self] # self
                             THEN /\ vc' = [vc EXCEPT ![self][m[self]] = SetMax({vc[self][m[self]],msg[self][m[self]], pt[self] - EPS} )]
                             ELSE /\ TRUE
                                  /\ vc' = vc
                       /\ m' = [m EXCEPT ![self] = m[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "J1"]
                  ELSE /\ vc' = [vc EXCEPT ![self][self] = SetMax({pt[self],vc[self][self],msg[self][self]+1})]
                       /\ pc' = [pc EXCEPT ![self] = "J0"]
                       /\ m' = m
            /\ UNCHANGED << pt, msg >>

Send(self) == /\ pc[self] = "Send"
              /\ (\A k \in Procs: pt[self] < pt[k]+ EPS)
              /\ pt' = [pt EXCEPT ![self] = pt[self] +1]
              /\ IF vc[self][self]<pt'[self]
                    THEN /\ vc' = [vc EXCEPT ![self][self] = pt'[self]]
                    ELSE /\ vc' = [vc EXCEPT ![self][self] = vc[self][self]+1]
              /\ \E k \in Procs \ {self}:
                   msg' = [msg EXCEPT ![k] = vc'[self]]
              /\ pc' = [pc EXCEPT ![self] = "J0"]
              /\ m' = m

j(self) == J0(self) \/ Recv(self) \/ J1(self) \/ Send(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        
Termination == <>(\A self \in ProcSet: pc[self] = "Done")  
  
\*Boundedness
TypeOK == (\A k \in Procs : vc[k][k] >= pt[k])
Sync == (\A k,n \in Procs: pt[k] <= pt[n]+EPS)
Boundedl == (\A k \in Procs: vc[k][k] >= pt[k] /\ vc[k][k] <= pt[k]+EPS) 
Boundedc == (\A k,p \in Procs: vc[k][k] >= vc[k][p]) 
\*Boundedness


\* END TRANSLATION
==================================================
