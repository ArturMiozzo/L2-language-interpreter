(*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L1               *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*++++++++++++++++++++++++++++++++++++++*)



(**+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

type tipo =
    TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo
  | TyRef of tipo
  | TyUnit

type ident = string

type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Var of ident
  | True
  | False
  | Binop of op * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr              
  | Asg of expr * expr
  | Dref of expr
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr
  | Skip
  
type tenv = (ident * tipo) list

type valor =
    VNum of int
  | VTrue
  | VFalse
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv 
and 
  renv = (ident * valor) list 
    
type v_env = V_Env of valor * renv    

(* funções polimórficas para ambientes *)

let rec lookup a k =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
       
let rec update a k i =
  (k,i) :: a   

(* exceções que não devem ocorrer  *)

exception BugParser
  
exception BugTypeInfer
  
  (**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)


exception TypeError of string


let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with

    (* TInt  *)
  | Num _ -> TyInt

    (* TVar *)
  | Var x ->
      (match lookup tenv x with
         Some t -> t
       | None -> raise (TypeError ("variavel nao declarada:" ^ x)))

    (* TBool *)
  | True  -> TyBool
  | False -> TyBool

    (*TOP+  e outras para demais peradores binários *)
  | Binop(oper,e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      if t1 = TyInt && t2 = TyInt then
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool)
      else raise (TypeError "operando nao é do tipo int")

    (* TPair *)
  | Pair(e1,e2) -> TyPair(typeinfer tenv e1, typeinfer tenv e2)
  (* TFst *)
  | Fst e1 ->
      (match typeinfer tenv e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "fst espera tipo par"))
    (* TSnd  *)
  | Snd e1 ->
      (match typeinfer tenv e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "fst espera tipo par"))

    (* TIf  *)
  | If(e1,e2,e3) ->
      (match typeinfer tenv e1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "then/else com tipos diferentes")
       | _ -> raise (TypeError "condição de IF não é do tipo bool"))

    (* TFn *)
  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)

    (* TApp *)
  | App(e1,e2) ->
      (match typeinfer tenv e1 with
         TyFn(t, t') ->  if (typeinfer tenv e2) = t then t'
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))

    (* TLet *)
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )

    (* TLetRec *)
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "tipo da funcao diferente do declarado")
  | LetRec _ -> raise BugParser
  
  | Asg(e1,e2) ->
      (match typeinfer tenv e1 with
         TyRef(t1) -> 
           let t2 = typeinfer tenv e2 in
           if t1 = t2 then TyUnit
           else raise (TypeError "tipos precisam ser iguais para atribuição")
       | _ -> raise (TypeError "tipo da variavel precisa ser ref para ser atribuida"))
  
  | Dref(e1) ->
      (match typeinfer tenv e1 with
         TyRef(t1) -> t1
       | _ -> raise (TypeError "tipo da variavel precisa ser ref para ser acessada"))
      
  | New(e1) ->
      let t1 = typeinfer tenv e1
      in TyRef(t1) 
  
  | Skip -> TyUnit
    
  | Whl(e1,e2) -> 
      ( match typeinfer tenv e1 with 
          TyBool -> 
            ( match typeinfer tenv e2 with 
                TyUnit -> TyUnit
              | _ -> raise (TypeError "segundo argumento precisa ser uma expressao do tipo unit"))
        | _ -> raise (TypeError "condição de Whl não é do tipo bool")) 
      
  | Seq(e1,e2) ->
      (match typeinfer tenv e1 with
         TyUnit -> typeinfer tenv e2
       | _ -> raise (TypeError "primeiro argumento precisa ser uma expressao do tipo unit"))
  
  
(**+++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*)




let compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with
    (Sum, VNum(n1), VNum(n2)) -> VNum (n1 + n2)
  | (Sub, VNum(n1), VNum(n2)) -> VNum (n1 - n2)
  | (Mult, VNum(n1),VNum(n2)) -> VNum (n1 * n2)
  | (Eq, VNum(n1), VNum(n2))  -> if (n1 = n2)  then VTrue else VFalse
  | (Gt, VNum(n1), VNum(n2))  -> if (n1 > n2)  then VTrue else VFalse
  | (Lt, VNum(n1), VNum(n2))  -> if (n1 < n2)  then VTrue else VFalse
  | (Geq, VNum(n1), VNum(n2)) -> if (n1 >= n2) then VTrue else VFalse
  | (Leq, VNum(n1), VNum(n2)) -> if (n1 <= n2) then VTrue else VFalse
  | _ -> raise BugTypeInfer


let rec eval (renv:renv) (e:expr) : v_env =
  match e with
    Num n -> V_Env(VNum n, renv)
  | True -> V_Env(VTrue, renv)
  | False -> V_Env(VFalse, renv)

  | Var x ->
      (match lookup renv x with
         Some v -> V_Env(v, renv)
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      (match eval renv e1 with V_Env(v1, renv') ->
         match eval renv' e2 with V_Env(v2, renv'') -> 
           V_Env((compute oper v1 v2), renv''))

  | Pair(e1,e2) ->
      (match eval renv e1 with V_Env(v1, renv') ->
         match eval renv' e2 with V_Env(v2, renv'') -> 
           V_Env(VPair(v1,v2), renv))

  | Fst e ->
      (match eval renv e with
       | V_Env(VPair(v1,_), renv') -> V_Env(v1, renv')
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match eval renv e with
       | V_Env(VPair(_,v2), renv') -> V_Env(v2, renv')
       | _ -> raise BugTypeInfer)


  | If(e1,e2,e3) ->
      (match eval renv e1 with
         V_Env(VTrue, renv') -> eval renv' e2
       | V_Env(VFalse, renv') -> eval renv' e3
       | _ -> raise BugTypeInfer )

  | Fn (x,_,e1) ->  V_Env(VClos(x,e1,renv), renv)

  | App(e1,e2) ->
      (match eval renv e1 with V_Env(v1, renv1) ->
         (match v1 with 
            VClos(x,ebdy,renv2) ->
              (match eval renv2 e2 with V_Env(v2, renv3) ->
                 let renv4 = update renv3 x v2
                 in eval renv4 ebdy)

          | VRclos(f,x,ebdy,renv2) ->
              (match eval renv2 e2 with V_Env(v2, renv3) ->
                 let renv4  = update renv3 x v2 in
                 let renv5 = update renv4 f v1
                 in eval renv5 ebdy)
          | _ -> raise BugTypeInfer))

  | Let(x,_,e1,e2) ->
      (match eval renv e1 with V_Env(v1, renv') ->
         let renv'' = update renv' x v1 in
         eval renv'' e2)

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2
        
        
  | LetRec _ -> raise BugParser
  
(* 
   implementação small step do asg 
  
| Asg(l,v) when (match lookup renv l with
        Some e -> true
      | None   -> false) ->
      let sigma_ = updateMem sigma l v in Em(Skip, sigma_)
  | Asg(v,e) when isvalue v ->
      (match step e sigma with Em(e', sigma') -> Em(Asg(v, e'), sigma'))

  | Asg(e1,e2) ->
      let l = eval renv e1 in
      let v = eval renv e2 in
      update renv 
        (match step e1 sigma with Em(e1', sigma') -> Em(Asg(e1', e2), sigma'))
*)

(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"

(* função auxiliar que converte valor para string *)

let rec vtos (mem: v_env) : string =
  match mem with
    V_Env(v, renv) -> 
      (match v with
         VNum n -> string_of_int n
       | VTrue -> "true"
       | VFalse -> "false"
       | VPair(v1, v2) ->
           "(" ^ (vtos (V_Env(v1, renv))) ^ "," ^ (vtos (V_Env(v2, renv))) ^ ")"
       | VClos _ ->  "fn"
       | VRclos _ -> "fn")

(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)
   
 (* as exceções abaixo nao podem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"
                        



 (* +++++++++++++++++++++++++++++++++++++++*)
 (*                TESTES                  *)
 (*++++++++++++++++++++++++++++++++++++++++*)



(*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 10 
*)

let e'' = Let("x", TyInt, Num 5, App(Var "foo", Num 10))

let e'  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e'')

let tst = Let("x", TyInt, Num(2), e') 
    
    (*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 
*)


let e2 = Let("x", TyInt, Num 5, Var "foo")

let e1  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e2)

let tst2 = Let("x", TyInt, Num(2), e1)