(* PROGETTO di LINGUAGGI 2013-14 Parte I ANALIZZATORE LESSICALE *)
(* la funzione I e' da fare   *)


datatype B = T | F ;

datatype token = KEYWORD of string  | OP of string | ID of string | SYM of string| NM of int | STR of string | BOOL of B| Nil ;

(*         Eccezioni      *)

exception NotValidChar of char;
exception UnexpectedEndOfString;
exception EmptyNumber;

(* fine Eccezioni *)

(* Analizzatore lessicale *)

(* Funzioni di supporto     *)
(* Testa se il carattere e' un carattere valido per iniziare
   un identificatore, un operatore o una keyword *)
fun IsAlphaChar(c: char) : bool =
  if (c >= (#"a") andalso c <=(#"z")) orelse (c>= (#"A") andalso c <= (#"Z")) 
  then true 
  else false;

(* riconosce se c e' un carattere numerico o no   *)
fun IsDigitChar(c)=
  if c>=(#"0") andalso c<= (#"9") 
  then
    true
  else
    false;

(* Testa se il carattere e' un carattere valido per comporre
   un identificatore, un operatore o una keyword (ad eccezione
   del primo carattere) *) 
fun IsIdChar(c: char) : bool =
  IsAlphaChar(c) orelse IsDigitChar(c);
  
(* Testa se il carattere e' un separatore *)
fun IsSeparator(c)=
  if  c= (#"(") orelse c=(#")") orelse c=(#"=") orelse c=(#"$") orelse c=(#",")
  then
    true
  else
    false;
(* testa se e' uno spazio o accapo *)

fun IsSpace(c)=
  if c=(#" ") orelse c=(#"\n") orelse c=(#"\f") orelse c=(#"\r") 
  then
    true
  else
    false;

fun IsOp(c)=
  if c=(#"+") orelse c=(#"-") orelse c=(#"*") orelse c=(#"/") 
  then
    true
  else
    false;
  

(* data una stringa X la confronta con le parole chiavi  e con gli operatori
del Lisp Kit e se e' una di queste cose, restituisce la corrispondente coppia
token_lexema, altrimenti la considera un identificatore e restituisce 
 la coppia (ID, STRINGA(X)) *)

fun extractWord("let": string) : token=
  KEYWORD("let") |
extractWord("in") =
  KEYWORD("in") |
extractWord("end") =
  KEYWORD("end") |
extractWord("letrec") =
  KEYWORD("letrec") |
extractWord("and") =
  KEYWORD("and") |
extractWord("nil") =
  Nil |
extractWord("true") =
  BOOL(T) |
extractWord("false") =
  BOOL(F) |
extractWord("eq") =
  OP("eq") |
extractWord("leq") =
  OP("leq") |
extractWord("car") =
  OP("car") |
extractWord("cdr") =
  OP("cdr") |
extractWord("cons") =
  OP("cons") |
extractWord("atom") =
  OP("atom") |
extractWord("if") =
  KEYWORD("if") |
extractWord("then") =
  KEYWORD("then") |
extractWord("else") =
  KEYWORD("else") |
extractWord("lambda") =
  KEYWORD("lambda") |
extractWord(s) =
  ID(s);
(* #endregion Funzioni di supporto *)

(* #Funzioni che implementano direttamente gli stati dell'automa. Osserva che non c'è ricorsione. Il passaggio dallo stato iniziale e principale I ad un altro stato è realizzato con un'invocazione. Poi si ritorna sempre a I e quindi basta il normale ritorno della funzione.
*)

(* Stato N per riconoscere i numeri *)

fun N(nil,n,b)= raise UnexpectedEndOfString |
N(c::l, n, b)=
  if IsDigitChar(c) 
  then
    let
      val x= ord(c)-ord(#"0")
    in 
      N(l, n*10+x ,b)
    end
else
  if b=true 
  then (NM(~n),c::l)
  else (NM(n),c::l);


(* Stato SC per riconoscere le stringhe tra virgolette    *)
fun SC(#"\""::l : char list, result : char list) : token*char list =
    (STR(implode(result)),l) |
SC(c::l, result) =
  SC(l, result@[c]) |
SC(nil, result) =
  raise UnexpectedEndOfString;
  

(* Stato S per raccogliere le stringhe che possono corrispondere
   ad identificatori, operatori prefissi o keyword *)
fun S(c::l: char list, result: char list) : token* char list=
  if IsIdChar(c) then
    S(l, result@[c])
  else 
    (extractWord(implode(result)),c::l)
|
S(nil, result) =
  raise UnexpectedEndOfString;
      

(*  FUNZIONE I DA FARE   *)

fun I(nil)= raise UnexpectedEndOfString |
I(x::xs) =
    if IsSpace(x) then I(xs)
    else if x = #"$" then [SYM(str(x))]
    
    else if x = #"~" then let 
            val res = N(xs, 0, true)
        in
            #1res::I(#2res)
        end
    else if IsDigitChar(x) then let
            val res = N(x::xs, 0, false)
        in
            #1res::I(#2res)
        end
    else if IsSeparator(x) then SYM(str(x))::I(xs)

    else if IsAlphaChar(x) then let
            val res = S(x::xs, [])
        in
            #1res::I(#2res)
        end
    else if x = #"\"" then let
            val res = SC(x::xs, [])
        in
            #1res::I(#2res)
        end
    else if IsOp(x) then OP(str(x))::I(xs)

    else raise NotValidChar(x);
(*_ _ _ _ _ _ _ _ _ _ _ *)


(* #FINE delle  Funzioni che implementano l'automa a stati finiti *)

(* Funzione principale per l'analisi lessicale *)
fun lexi(s : char list) :  token list =
  I(s);

(* #endregion Analizzatore lessicale *)


(* esempi di programmi in Lisp Kit per provare lexi *)

(* val C="letrec  FACT = lambda ( X ) if  eq ( X 0 ) then 1 else  X*FACT(  X- 1 ) and G = lambda ( H L ) if  eq ( L  nil ) then L else cons( H(car( L ) ) G ( H cdr ( L ) )) in G ( FACT cons(1 cons(2 cons(3 nil))) ) end $"; *)

(* val C="letrec  FACT = lambda ( X ) if  eq ( X 0 ) then 1 else  X*FACT(  X- 1 )and G = lambda ( H L ) if  eq ( L  nil ) then L else cons( H(car( L ) ) G ( H cdr ( L ) )) in G ( FACT cons(1 cons(2 cons(3 nil))) ) end $"; *)

(* val D= "let x=cons(\"ab\" cons(\"cd\" nil)) in if true then cons(\"01\" x) else nil end $"; *)

