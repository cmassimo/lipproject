(* PARSER LispKit  incompleto Novembre 2013*)

Control.Print.printDepth := 20;
Control.Print.printLegth := 20;

use "analizzatore-lessicale.ml";

(* richiamare l'analizzatore lessicale *)

(*         Eccezioni      *)

exception NOCONST;
exception Etwo of string*string;
exception ex of string;
(* fine Eccezioni *)


(* funzioni per DEBUG ***************************)

fun f(x : token) : string=
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
    g(h::t)= f(h) ^ g(t);


(*  AUSILIARIA *****************************)
fun trova_stringa(nil, x)= raise ex("la stringa termina prematuramente") |
    trova_stringa(KEYWORD(a)::z, x)= a = x |
    trova_stringa(OP(a)::z, x)= a = x |
    trova_stringa(ID(a)::z, x)= a = x |
    trova_stringa (SYM(a)::z, x)= a = x |
    trova_stringa(STR(a)::z, x)= a = x |
    trova_stringa(_, _)= false;


datatype LKC=
  VAR of string |
  NUM of int |
  BOO of B |
  STRI of string |
  NIL |
  ADD of LKC*LKC |
  SUB of LKC*LKC |
  MULT of LKC*LKC |
  DIV of LKC*LKC |
  EQ of LKC*LKC |
  LEQ of LKC*LKC |
  CAR of LKC |
  CDR of LKC |
  CONS of LKC*LKC |
  ATOM of LKC |
  IF of LKC*LKC*LKC |
  LAMBDA of LKC list * LKC |
  CALL of LKC * LKC list |
  LET of LKC * (LKC*LKC) list |
  LETREC of LKC * (LKC*LKC) list;

(* Analizzatore sintattico ****************************)
val PROG =
  let (* usare la let forma una specie di namespace evitando involontari conflitti di nome tra le funzioni definite
nelle diverse parti del programma *)

    fun
    Prog(nil)= raise ex("Prog: terminazione imprevista") |
    Prog(KEYWORD(a)::c)=
      if not(a = "let" orelse a = "letrec")
      then 
        raise ex("programma inizia senza let/letrec")
      else

        let 
          val (trad_bind, bind) = Bind(c)
        in
          if not(trova_stringa(bind, "in")) 
          then raise Etwo("Prog: no in dopo bind", g(bind))
          else

            let 
              val (trad_exp, exp) = Exp(tl(bind))
            in
              if not(trova_stringa(exp, "end"))
              then 
                raise Etwo("no end alla fine del programma", g(exp))
              else if (a = "let")
                then (LET(trad_exp, trad_bind), tl(exp))
                else (LETREC(trad_exp, trad_bind), tl(exp))
            end

        end |
    Prog(_)= raise ex("programma inizia senza keyword")
      
    and

    Exp(nil)= raise ex("Exp: input termina prematuramente") |
    Exp(KEYWORD("let")::c)= Prog(KEYWORD("let")::c) |
    Exp(KEYWORD("letrec")::c)= Prog(KEYWORD("letrec")::c) |
    Exp(KEYWORD("lambda")::c)=
      let
        val (trad_lambda, lmbd) = esp_LAMB(c)
        val (trad_exp, exp) = Exp(lmbd)
      in
        (LAMBDA(trad_lambda, trad_exp), exp)
      end |
    Exp(OP("cons")::c)= let val (trad_cons, cns) = due_exp(c) in (CONS(trad_cons), cns) end |
    Exp(OP("car")::c)= let val (trad_exp, exp) = Exp(c) in (CAR(trad_exp), exp) end |
    Exp(OP("cdr")::c)= let val (trad_exp, exp) = Exp(c) in (CDR(trad_exp), exp) end |
    Exp(OP("eq")::c)= let val (trad_exp, exp) = due_exp(c) in (EQ(trad_exp), exp) end |
    Exp(OP("leq")::c)= let val (trad_exp, exp) = due_exp(c) in (LEQ(trad_exp), exp) end |
    Exp(OP("atom")::c)= let val (trad_exp, exp) = Exp(c) in (ATOM(trad_exp), exp) end |
    Exp(KEYWORD("if")::c)= 
      let 
        val (trad_exp, exp)= Exp(c)
      in
        if not (trova_stringa(exp, "then"))
        then
          raise Etwo("dopo if exp niente then", g(exp))
        else
          let 
            val (trad_then, thn) = Exp(tl(exp))
          in
            if not(trova_stringa(thn, "else"))
            then 
              raise Etwo("dopo if_then niente else", g(thn))
            else
              let val (trad_else, els) = Exp(tl(thn)) in (IF(trad_exp, trad_then, trad_else), els) end
          end
      end | (* espressioni aritmetiche *)
    Exp(tlist)= ExpA(tlist) (*5 ExpA::= T E1 *)
      
    and

    ExpA(nil)= raise ex("ExpA: input termina prematuramente") |
    ExpA(tlist)= let val (trad_t, texp) = T(tlist) in E1(trad_t, texp) end

    and

    E1(PO : LKC, nil)= raise ex("E1: input termina prematuramente") |
    E1(PO : LKC, OP("+")::c)= let val (trad_t, texp) = T(c) in E1(ADD(PO, trad_t), texp) end |
    E1(PO : LKC, OP("-")::c)= let val (trad_t, texp) = T(c) in E1(SUB(PO, trad_t), texp) end |
    E1(PO : LKC, tlist) = (PO, tlist)

    and

    T(nil)= raise ex("T: input termina prematuramente") |
    T(tlist)= let val (trad_f, fexp) = F(tlist) in T1(trad_f, fexp) end

    and

    T1(PO : LKC, nil)= raise ex("T1: input termina prematuramente") |
    T1(PO : LKC, OP("*")::c)= let val (trad_f, fexp) = F(c) in T1(MULT(PO, trad_f), fexp) end |
    T1(PO : LKC, OP("/")::c)= let val (trad_f, fexp) = F(c) in T1(DIV(PO, trad_f), fexp) end |
    T1(PO : LKC, tlist) = (PO, tlist)

    and 

    Exp_const(nil)= raise ex("Exp_const: input termina prematuramente") |
    Exp_const(NM(a)::c : token list)= (NUM(a), c) |
    Exp_const(Nil::c)= (NIL, c) |
    Exp_const(BOOL(a)::c)= (BOO(a), c) |
    Exp_const(STR(a)::c)= (STRI(a), c) |
    Exp_const(tlist)= raise NOCONST

    and

    F(nil)= raise ex("F: input termina prematuramente") |
    F(tlist)= Exp_const(tlist) handle NOCONST =>
      if (trova_stringa(tlist, "("))
      then
        let
          val (trad_expa, expa) = ExpA(tlist)
        in
          if not(trova_stringa(expa, ")"))
          then raise Etwo("manca ) dopo (ExpA", g(expa))
          else (trad_expa, tl(expa))
        end
      else
        let
          val (trad_var, var_exp) = var(tlist)
        in
          if (trova_stringa(var_exp, "("))
          then
            let
              val (trad_y, yexp) = Y(var_exp)
            in
              (CALL(trad_var, trad_y), yexp)
            end
          else 
            (trad_var, var_exp)
        end
    (* espressione non costante *)

    and

    Y(nil)= raise ex("Y: input termina prematuramente") |
    Y(SYM("(")::c)=
      let
        val (trad_seqexp, seqexp) = Seq_Exp(c)
      in
        if not(trova_stringa(seqexp, ")"))
        then raise Etwo("Y: manca ) dopo Seq_Exp", g(seqexp))
        else (trad_seqexp, tl(seqexp))
      end |
    Y(tlist) = (nil, tlist)

    and

    Seq_Exp(nil)= raise ex("Seq_Exp: input termina prematuramente") |
    Seq_Exp(tlist)=
      if not(trova_stringa(tlist, ")")) (* non sono nella produzione epsilon *)
      then
        let
          val (trad_exp, exp) = Exp(tlist)
          val (trad_z, zexp) = Z(exp)
        in
          (trad_exp::trad_z, zexp)
        end
      else (nil, tlist)

    and

    Z(nil)= raise ex("Z: input termina prematuramente") |
    Z(SYM(",")::c)= let val (trad_seqexp, seqexp) = Seq_Exp(c) in (trad_seqexp, seqexp) end |
    Z(tlist)= (nil, tlist)

    and

    Seq_Var(nil)= raise ex("Seq_Var: la stringa termina prematuramente") |
    Seq_Var(tlist)=
      if not(trova_stringa(tlist, ")"))
      then
        let
          val (trad_var, var_exp) = var(tlist)
          val (trad_seqvar, seqvar) = Seq_Var(var_exp)
        in
          (trad_var::trad_seqvar, seqvar)
        end
      else (nil, tlist) (* non consumo la ) che va consumata in Exp *)

    and

    var(nil)= raise ex("var: la stringa termina prematuramente") |
    var(ID(a)::c)= (VAR(a), c) |
    var(tlist)= raise Etwo("oggetto estraneo in Var_List", g(tlist))

    (*2 Bind::= var = Exp X 3 X::= and Bind | epsilon *)

    and

    Bind(nil)= raise ex("Z: input termina prematuramente") |
    Bind(tlist)=
      let
        val (trad_var, var_exp) = var(tlist)
      in
        if not(trova_stringa(var_exp, "="))
        then raise Etwo("Bind: manca = dopo var in Bind", g(var_exp))
        else
          let
            val (trad_exp, exp) = Exp(tl(var_exp))
            val (trad_x, xexp) = X(exp)
          in
            ((trad_var, trad_exp)::trad_x, xexp)
          end
      end

    and

    X(nil)= raise ex("X: input termina prematuramente") |
    X(KEYWORD("and")::c)= Bind(c) |
    X(tlist)= (nil, tlist)

    and

    esp_LAMB(c)= (* serve per riconoscere la sequenza di parametri formali di una lambda *)
      if not(trova_stringa(c, "("))
      then raise ex("esp_LAMB: manca (")
      else 
        let 
          val (trad_seqvar, seqvar) = Seq_Var(tl(c))
        in
          if trova_stringa(seqvar,")")
          then (nil, tl(seqvar))
          else raise ex("non si chiude la )")
        end

    and

    due_exp(c)=
      if not (trova_stringa(c, "("))
      then raise ex("la stringa termina prematuramente")
      else 
        let 
          val (trad_exp, exp) = Exp(tl(c)) 
        in
          if trova_stringa(exp, ",")
          then

            let
              val (trad_exp2, exp2) = Exp(tl(exp))
            in
              if trova_stringa(exp2, ")")
              then ((trad_exp, trad_exp2), tl(exp2))
              else raise ex("non si chiude la )")
            end

          else raise Etwo("non c'e' , tra 2 expr",g(exp)) 
        end


  in
    Prog
  end;

 
  (*esempi per test*)


(*val S="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X - 1 )"^
"and G = lambda ( H L ) if  eq ( nil, L ) then L else cons( H(car( L ) ),"^ 
"G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $";
*)


val S= "let x= 5 and y= 6 in x * 3 + y * 2 * x + x * y end $";






(*val S="letrec PP = lambda ( x ) if eq ( x , 1) then 1 else"^
"  x * PP( x - 1 ) in  PP( 3 ) end $ ";*)



val D = lexi(explode(S));

val asd = let
  val q = (PROG(D) 
    handle Etwo(x,y)=> let val a = print("ERRORE "^x) and b = print("\n") and c = print(y) in (NIL, nil) end
    handle ex(s) => let val a = print(s) in (NIL, nil) end
    handle NOCONST => let val a = print("NOCONST") in (NIL, nil) end)
in 
  case q of
    (NIL, nil) => NIL |
    (x, SYM(a)::t) => x |
    (_, _) => NIL
end;

