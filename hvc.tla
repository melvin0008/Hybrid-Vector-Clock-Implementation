-------------------- MODULE hvc -------------------
EXTENDS Integers
CONSTANT N, STOP, EPS
ASSUME N \in Nat \ {0,1}
Procs == 1..N

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

(* Hybrid Logical Clocks algorithm
--algorithm hvc {
  variable pt = [j \in Procs |-> 0], msg= [j \in Procs |-> [k \in Procs |-> 0]]; \* shared/aux vars

  fair process (j \in Procs)
  {J0:while (pt[self] < STOP)
      {either 
       Recv:{ \* local or receive event
         \* if not heard increase msg[self][not heard]= msg[self][not heard] + EPS
         await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
            
            
            
            
            } 
       or
       Send:{ \* send event
         await(\A k \in Procs: pt[self] < pt[k]+ EPS); \* NTP clock sync
            pt[self] := pt[self] +1;
            msg[self][self] := msg[self][self] + 1;         
      } 
  }
}

*)
==================================================