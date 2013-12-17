(* PARSER LispKit  incompleto Novembre 2013*)

use "assegnamento-lex.ml.ml";

(* richiamare l'analizzatore lessicale *)

(*         Eccezioni      *)

exception NOCONST;
exception Etwo of string*string;
exception ex of string;
(* fine Eccezioni *)


(* funzioni per DEBUG ***************************)

fun f(x:token):string=
case x of 
KEYWORD(a) => a |
ID(a) => a |
OP(a)=> a |
SYM(a)=> a |
STR(a)=> a |
NM(a) => "NM" |
BOOL(a)=> "BOOL" |
Nil => "Nil";
(*_=> "oggetto non previsto";*)

fun g(nil)= "" |
g(h::t)=  f(h) ^ g(t);


(*  AUSILIARIA *****************************)
fun trova_stringa(nil,x)=
  raise ex("la stringa termina prematuramente") |
  trova_stringa(KEYWORD(a)::z,x)= a=x |
  trova_stringa(OP(a)::z,x)= a=x |
  trova_stringa(ID(a)::z,x)= a=x |
  trova_stringa (SYM(a)::z,x)=a=x |
  trova_stringa(STR(a)::z,x)= a=x|
  trova_stringa(_,_)= false;

(* Analizzatore sintattico ****************************)
val PROG= let (* usare la let forma una specie di namespace evitando involontari conflitti di nome tra le funzioni definite
nelle diverse parti del programma *)

  fun
  Prog (nil): token list =
    raise ex("Prog: terminazione imprevista")
  |

  Prog(KEYWORD(a)::c)=
    if not(a="let" orelse a="letrec")
      then 
        raise ex("programma inizia senza let/letrec")
      else

        let 
          val x1=Bind(c) 
        in
          if not(trova_stringa(x1,"in")) 
            then raise Etwo("Prog: no in dopo bind",g(x1))
            else

              let 
                val x2=Exp(tl(x1)) 
              in
                if not(trova_stringa(x2,"end"))
                  then 
      	           raise Etwo("no end alla fine del programma", g(x2) )
                  else 
      	           tl(x2)
              end

        end
  |

  Prog(_)= raise ex("programma inizia senza keyword")
    
  and

  Exp(nil)=
    raise ex("Exp: input termina prematuramente")
  |
  Exp(KEYWORD("let")::c)= Prog(KEYWORD("let")::c)
  |
  Exp(KEYWORD("letrec")::c)= Prog(KEYWORD("letrec")::c)
  |
  Exp(KEYWORD("lambda")::c)= Exp(esp_LAMB(c))
  |
  Exp(OP("cons")::c) = due_exp(c)
  |     
  Exp(OP("car")::c) = Exp(c)
  |     
  Exp(OP("cdr")::c) = Exp(c) 
  |     
  Exp(OP("eq")::c) = due_exp(c)
  |     
  Exp(OP("leq")::c) = due_exp(c)
  |     
  Exp(OP("atom")::c) = Exp(c)
  |     
  Exp(KEYWORD("if")::c) = 
    let 
      val x1=Exp(c)
    in
      if not (trova_stringa(x1,"then"))
      then
        raise Etwo("dopo if exp niente then",g(x1))
      else
        let 
          val x2=Exp(tl(x1))
        in
          if  not(trova_stringa(x2,"else"))
          then 
            raise Etwo("dopo if_then niente else",g(x2))
          else
            Exp(tl(x2))
        end
    end
  | (* espressioni aritmetiche *)
    
  Exp(x)= ExpA(x) (*5 ExpA::= T E1 *)
    
  and

  ExpA(nil)=
    raise ex("ExpA: input termina prematuramente")
  |
  ExpA(x) = E1(T(x))

  and

  E1(nil)=
    raise ex("E1: input termina prematuramente")
  |
  E1(OP("+")::c) = E1(T(c))
  |
  E1(OP("-")::c) = E1(T(c))
  |
  E1(s) = s

  and

  T(nil)=
    raise ex("T: input termina prematuramente")
  |
  T(x) = T1(F(x))

  and

  T1(nil)=
    raise ex("T1: input termina prematuramente")
  |
  T1(OP("*")::c) = T1(F(c))
  |
  T1(OP("/")::c) = T1(F(c))
  |
  T1(s) = s

  and 

  Exp_const(nil):token list= 
    raise ex("Exp_const: input termina prematuramente")
  |
  Exp_const(NM(a)::c:token list)= c
  |
  Exp_const(Nil::c)=c
  |
  Exp_const(BOOL(a)::c)= c
  |
  Exp_const(STR(a)::c)= c
  |
  Exp_const(a)= raise NOCONST

  and

  F(nil)=
    raise ex("F: input termina prematuramente")
  |
  F(x)= Exp_const(x) handle NOCONST =>
    if (trova_stringa(x, "("))
    then
      let
        val ea = ExpA(x)
      in
        if not(trova_stringa(ea, ")"))
        then raise Etwo("manca ) dopo (ExpA", g(ea))
        else tl(ea)
      end
    else Y(var(x))
  (* espressione non costante *)

  and

  Y(nil)=
    raise ex("Y: input termina prematuramente")
  |
  Y(SYM("(")::c)=
    let
      val se = Seq_Exp(c)
    in
      if not(trova_stringa(se, ")"))
      then raise Etwo("Y: manca ) dopo Seq_Exp", g(se))
      else tl(se)
    end
  |
  Y(s) = s

  and

  Seq_Exp(nil)=
    raise ex("Seq_Exp: input termina prematuramente")
  |
  Seq_Exp(s) =
    if not(trova_stringa(s, ")")) (* non sono nella produzione epsilon *)
      then Z(Exp(s))
      else s

  and

  Z(nil)= 
    raise ex("Z: input termina prematuramente")
  |
  Z(SYM(",")::c)= Seq_Exp(c)
  |
  Z(s)= s

  and

  Seq_Var(nil):token list=
    raise ex("Seq_Var: la stringa termina prematuramente")
  |
  Seq_Var(x)=
    if not(trova_stringa(x,")"))
      then
        Seq_Var(var(x))
      else
        x (* non consumo la ) che va consumata in Exp *)

  and

  var(nil):token list =
    raise ex("var: la stringa termina prematuramente")
  |
  var(ID(a)::c)= c 
  |
  var(x)= raise Etwo("oggetto estraneo in Var_List", g(x))

  (*2 Bind::= var = Exp X 3 X::= and Bind | epsilon *)

  and

  Bind(nil)=
    raise ex("Z: input termina prematuramente")
  |
  Bind(s)=
    let
      val va = var(s)
    in
      if not(trova_stringa(va, "="))
        then raise Etwo("Bind: manca = dopo var in Bind", g(va))
        else X(Exp(tl(va)))
    end

  and

  X(nil)=
    raise ex("X: input termina prematuramente")
  |
  X(KEYWORD("and")::c)= Bind(c)
  |
  X(s)= s

  and

  esp_LAMB(c)= (* serve per riconoscere la sequenza di parametri formali di una lambda *)
    if not (trova_stringa(c,"("))
    then 
      raise ex("esp_LAMB: manca (")
    else 
      let 
        val c1=Seq_Var(tl(c)) 
      in
        if trova_stringa(c1,")")
          then 
  	       tl(c1)
          else
            raise ex("non si chiude la )")
      end

  and

  due_exp(c):token list=
    if not (trova_stringa(c,"("))
    then 
      raise ex("la stringa termina prematuramente")
    else 
      let 
        val c1 =Exp(tl(c)) 
      in
        if trova_stringa(c1,",")
        then
          let
            val c2= Exp(tl(c1))
          in
            if trova_stringa(c2,")")
            then 
              tl(c2)
            else
              raise ex("non si chiude la )")
          end
        else
          raise Etwo("non c'e' , tra 2 expr",g(c1)) 
      end

  in
    Prog
  end;

 
  (*esempi per test*)


val S="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X - 1 )"^
"and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) ),"^ 
"G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";



(*val S= "let x= 5 and y= 6 in x * 3 + y * 2 * x + x * y end $";*)






(*val S="letrec PP = lambda ( x ) if eq ( x , 1) then 1 else"^
"  x * PP( x - 1 ) in  PP( 3 ) end $ ";*)



val D= lexi(explode(S));

let val q=(PROG(D) 
  handle Etwo(x,y)=> let val a=print("ERRORE "^x) and b=print("\n") and c=print(y) in nil end
  handle ex(s) => let val a =print(s) in nil end
  handle NOCONST => let val a=print("NOCONST") in nil end)
in 
  case q of
    nil => "Bad 1" |
    (SYM(a)::t) => a |
    _ => "Bad 2"
end;

