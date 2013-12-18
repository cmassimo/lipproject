(*INTERPRETE SECD COMPLETO Novembre 2013*)

use "compilatore.ml";

(* tipo che modella gli R-valori delle variabili. Si tratta dei valori da mettere nella pila S e nell'ambiente dinamico E. In 
particolare CLO modella le chiusure.  *)

(* OGA= place holder per l'ambiente *)
datatype Valore = V of LKC| OGA |
                  CLO of secdexpr list * (unit -> Valore list list)| 
                  VLISTA of Valore list ;
		  

exception Error of string; 
exception Vuota_Hd;
exception Vuota_Tl;

(* funzioni ausiliarie *)

fun HA(a:'a list):'a =
case a of 
[]=> raise Vuota_Hd |
x::y => x;

fun TA(a:'a list):'a list = 
case a of
[]=> raise Vuota_Tl | 
x::y => y;

(* funz che crea l'ambiente dinamico ricorsivo necessario per il trattamento della ricorsione. Serve nel caso Rap *)

fun LazyE([],_):Valore list = [] |
LazyE(a::b,A)= LazyClo(a,A)::LazyE(b,A)

and

LazyClo(CLO(a,b),A)= let val w=b() in CLO(a, fn()=> LazyE(A,A)::w) end 
|
LazyClo(V(x),A)=V(x) 
|
LazyClo(VLISTA(x),A)=VLISTA(x)
|
LazyClo(_,_)=raise Error("LazyClo trova valore non possibile");

(* datatype dei valori del Dump *)

datatype Dump = CONTR of secdexpr list | 
                TRIPLA of Valore list * Valore list list * secdexpr list |
		DUMMY;

(* funzioni per la ricerca degli R-valori dati i loro indirizzi: usate da Ld *)

fun index (n: int, s: 'a list): 'a=
           if n=0 then HA(s) else index(n-1,TA(s));  


fun locate((a,b):int*int, e: Valore list list):Valore=
  index(b,index(a,e));
      
val extract_int   = fn V(NUM(x)) => x |
                    _ => raise Error("trovato altro da intero");

(* funzioni per le liste di Valori VLISTA *)

val Vhd = fn VLISTA(a::b) => a |
          Q  => raise Error("Vhd fallisce");

 fun  Vtl(VLISTA(a::b)) = VLISTA(b)  |
    Vtl(_)  = raise Error("Vtl fallisce");


fun Vatom(a : Valore):Valore=
  case a of 
   V(K) => V(BOO(T))
  |
   Q1 => V(BOO(F));         
                                        
fun bool2s_espressione(b: bool): LKC=
         if b then BOO(T) else BOO(F);

(* test di uguaglianza per il tipo Valore, si adatta ai tipi dei parametri con cui � invocata*)

fun EqValore(a,b)= 
case a of 
V(_)=> EqV(a,b) |
VLISTA(_)=> EqVLISTA(a,b)|
_=> raise Error("uguaglianza tra chiusure")

and EqVLISTA(VLISTA([]),VLISTA([]))= true |
EqVLISTA(VLISTA(a::b), VLISTA(c::d)) = EqValore(a,c) andalso EqVL(b,d)|
EqVLISTA(x,y)= false

and 
EqV(V(a), x):bool= (case x of
V(b)=>  (a=b) |
_=> false) |
EqV(a,b)= false

and
EqVL([],[]) = true |
EqVL(a::b ,c::d)= (EqValore(a,c) andalso EqVL(b,d))|
EqVL(_,_)= false;
 
(* FUNZIONE PRINCIPALE   *)

fun interprete(S: Valore list, E: Valore list list, C: secdexpr list, D: Dump list):Valore =  
case HA(C) of           
           Ld(b,n) => 
              let 
                val x = locate((b,n),E) handle VuotoHd => raise Error("in locate")
              in 
                interprete(x::S,E,TA(C),D)
              end 
              |           
	      Ldc(k) => 
		     
		     (case k of 
		     NIL => interprete(VLISTA([])::S,E,TA(C),D)|
		     x => interprete(V(k)::S,E,TA(C),D))
                 |
              Add =>
              let 
                val operand1 = extract_int(HA(S));
                val operand2 = extract_int(HA(TA(S)));
              in  
                interprete(V(NUM(operand1 + operand2))::TA(TA(S)),E,TA(C),D)
             end 
                |
             
            Sub =>
              let 
                val operand1 = extract_int(HA(S)handle VuotoHd =>(print("SUB1");V(NIL)));
                val operand2 = extract_int(HA(TA(S))handle VuotoHd =>(print("SUB2");V(NIL)));
		 
              in  
                interprete(V(NUM(operand1 - operand2))::TA(TA(S)),E,TA(C),D)
             end |
            
            Mult =>
              let 
                val operand1 = extract_int(HA(S)handle VuotoHd =>(print("MULT1");V(NIL)));
                val operand2 = extract_int(HA(TA(S))handle VuotoHd =>(print("MULT2");V(NIL)));
              in  
                interprete(V(NUM(operand1*operand2))::TA(TA(S)),E,TA(C),D)
             end |
            
             Div =>
              let 
                val operand1 = extract_int(HA(S));
                val operand2 = extract_int(HA(TA(S)));
              in  
                interprete(V(NUM (operand1 div operand2))::TA(TA(S)),E,TA(C),D)
             end |
          
	    Rem =>
              let 
                val operand1 = extract_int(HA(S));
                val operand2 = extract_int(HA(TA(S)));
              in  
                interprete(V(NUM (operand1 mod operand2))::TA(TA(S)),E,TA(C),D)
             end |
             
             Leq =>
              let 
                val operand1 = extract_int(HA(S));
                val operand2 = extract_int(HA(TA(S)));
              in  
                interprete(V(bool2s_espressione(operand1 <= operand2))::TA(TA(S)),E,TA(C),D)
             end |
           
              Eq => (case S of 
		      w1::w2::w3 => interprete(V(bool2s_espressione(EqValore(w1,w2)))::w3,E,TA(C),D)|
		      _=> raise Error("manca un argomento in Eq"))
		                      
		 |
              Car => 
                 interprete(Vhd(HA(S)handle VuotoHd =>(print("CAR");V(NIL)))::TA(S),E,TA(C),D) 
		 |
 
              Cdr => 
                 interprete(Vtl(HA(S)handle VuotoHd =>(print("CDR");V(NIL)))::TA(S),E,TA(C),D)
		 |
              
              Cons => 
                 (case HA(TA(S))handle VuotoHd =>(print("CONS");V(NIL)) of 
                      VLISTA([])=>
                         interprete(VLISTA([HA(S)handle VuotoHd =>(print("CONS2");V(NIL))])::TA(TA(S)),E,TA(C),D) | 
                      
                      VLISTA(vl2) =>
                         interprete(VLISTA((HA(S)handle VuotoHd =>(print("CONS3");V(NIL)))::vl2)::TA(TA(S)),E,TA(C),D)| 
		      _ => 
		         raise Error("CONS: il secondo argomento non e' una lista"))
                     |                                   
                    
                 Atom => 
                 interprete(Vatom(HA(S))::TA(S),E,TA(C),D)
		     |
            
		 Sel(sl1,sl2) =>
                 
                   (case HA(S)handle VuotoHd =>(print("SEL");V(NIL)) of
                         V(BOO(T)) => interprete(TA(S), E, sl1,CONTR(TA(C))::D)|
                         V(BOO(F)) => interprete(TA(S), E, sl2, CONTR(TA(C))::D)|
                         _ =>  raise Error("SEL: non trovato bool su S"))
                 | 
               
              Join => 
                   (case HA(D)handle VuotoHd =>(print("JOIN");DUMMY) of 
                             CONTR(C1) => interprete(S,E,C1,TA(D))| 
                             _=> raise 
			     Error("JOIN: il dump non contiene controllo") )
                   |

              Ldf(sl) =>
                      interprete(CLO(sl,fn()=>E)::S,E,TA(C),D)
		   |
              
              Ap =>
                    (case HA(S) handle VuotoHd =>(print("AP");V(NIL)) of
		     CLO(c1,e1)=> 
		        (case HA(TA(S))handle VuotoHd =>(print("AP2");V(NIL)) of
			       VLISTA([]) => interprete([],[]::e1(), c1,TRIPLA(TA(TA(S)),E,TA(C))::D)| 
			       VLISTA(vl2) => interprete([],vl2::e1(), c1,TRIPLA(TA(TA(S)),E,TA(C))::D)| 
			       X=> raise Error("AP: non ci sono i parametri attuali"))|
		      _ => raise Error("AP: non trovata chiusura su S"))	                      
                 | 

                 Rtn => 
                        (case HA(D)handle VuotoHd =>(print("RTN");DUMMY) of 
			TRIPLA(s1,e1,c1)=>    interprete(HA(S)::s1,e1,c1,TA(D))|
 			_ =>  raise Error("RTN: non trovata TRIPLA su dump"))   
                               
        | 
		Rap => 	(case HA(S) of
			    CLO(c1,e1)=>  let val O::re=e1()in 
                                                  case O of 
                                                        [OGA] => (case HA(TA(S)) of
			                                                            VLISTA(vl2) => 
			                                                              interprete([],LazyE(vl2,vl2)::re, c1, TRIPLA(TA(TA(S)),TA(E),TA(C))::D) 
		                                                                |
		                                                                 _  => raise Error("RAP: non trovo i parametri attuali dell'invocazione"))
                                                        |
                                                        _=> raise Error("ambiente senza OGA trovato da Rap")	
                                                  end	        
		        |
		         _ => raise Error("Rap: non trovata chiusura su S"))  
                                                                 
        | 
        Push => interprete(S, [OGA]::E,TA(C),D)
        |
        Stop => HA(S)
		|
		_ => (print("operazione non riconosciuta"); V(NIL)) ;
		


(* Mostra che si puo' usare letrec anche con binders non-funzionali. Le var a sinistra non devono apparire a destra *)
val S= "let z=2 in letrec x= 2+z and y= 2*z in x*y*z end end $";

(* distribuisce FACT su una lista di interi

val S="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X * FACT(  X - 1 )"^
" and G = lambda ( H  L ) if  eq ( nil, L ) then L else cons( H(car( L ) ), G ( H , cdr ( L ) ))"^
" in G ( FACT, cons( 6 ,cons( 7, cons( 8 , nil))) ) end $"; *)

(*considera liste di liste Z e produce una lista semplice che contiene tanti interi quante sono le liste contenute in Z e l'intero 
corrispondente ad una lista contenuta in Z � la somma dei fattoriali dei suoi elementi: f2=fattoriale, f1=calcola somma dei fattoriali degli elementi di una 
lista di interi e f0 distribuisce f1 sulle liste contenute in Z

val S="letrec f0 = lambda ( x ) letrec f1 = lambda(y) letrec f2=lambda (z) if eq(z , 1) then 1 else z * f2( z - 1 ) "^
"in if eq( y , nil ) then 0 else f2 ( car ( y ) ) + f1 ( cdr (y)) end "^
"in if eq(x , nil) then nil else cons (f1 ( car ( x )),f0 ( cdr ( x ) ) ) end "^
"in f0( cons (cons (3 , cons (3 , nil)), cons( cons (3 , nil), nil))) end $"; *)


(* esempio di funzione che restituisce una funzione locale

val S="let f1 = lambda() letrec f2=lambda (z) if eq(z , 1) then 1 else z * f2( z - 1 ) "^
"in f2 end in let x=f1() in x(8) end end $"
*)

val Tok=lexi(explode(S));

val (k1,k2)=PROG(Tok) 
handle Etwo(x,y)=> let val a=print("ERRORE "^x) and b=print("\n") and c=print(y) in (VAR "", nil) end
handle ex(s) => let val a =print(s) in (VAR "",nil) end
handle NOCONST => let val a=print("NOCONST") in (VAR "",nil) end;

val SE=COMP(k1,[],[]);
val fin=interprete([],[],SE@[Stop],[]);
