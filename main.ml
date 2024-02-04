(*++++++++++++++++++++++++++++++++++++++*)
(*    Trabalho de Semântica Formal      *)
(*        Artur Chika Miozzo            *)
(*        Eric Cidade Mathias           *)
(*++++++++++++++++++++++++++++++++++++++*)

(*++++++++++++++++++++++++++++++++++++++*)
(*        Interpretador para L2         *)
(*   - inferência de tipos              *)
(*   - avaliador big step com ambiente  *)
(*   - L1 com construções imperativas   *)
(*++++++++++++++++++++++++++++++++++++++*)

(**+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

(* exceções que não devem ocorrer  *)

exception BugParser
  
exception BugTypeInfer
  
exception ElementNotInList of string

exception TypeError of string
    
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
  | Vl of int
  | VSkip
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv 
and 
  renv = (ident * valor) list

type mem = (int * valor) list
    
type v_mem = V_Mem of valor * mem

(* funções polimórficas para ambientes *)

let rec lookup a k =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
          
let rec update a k i =
  (k,i) :: a   

let rec update_mem a k i =
  match a with
    [] -> raise (ElementNotInList ("Endereço " ^ string_of_int k ^ "não encontrado na memória"))
  | (y,i') :: tl -> (if (y=k) then ((y,i) :: tl) else ((y,i') :: (update_mem tl k i)))
                    
let rec lookup_mem a k =
  match a with
    [] -> raise (ElementNotInList ("Endereço " ^ string_of_int k ^ "não encontrado na memória"))
  | (y,i) :: tl -> if (y=k) then i else lookup_mem tl k

          
let rec count_mem a =
  match a with
    [] -> 0
  | (y,i) :: tl -> 1 + count_mem tl
          
let rec alloc_mem a k : v_mem =
  let i = count_mem(a) in 
  V_Mem(Vl i, (i,k) :: a)
  

(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  | TyRef(t) -> "ref " ^ (ttos t)
  | TyUnit -> "unit"

(* função auxiliar que converte valor para string *)

let rec vtos (value: valor) : string =
  (match value with
     VNum n -> string_of_int n
   | VTrue -> "true"
   | VFalse -> "false"
   | Vl n -> "l " ^ string_of_int n
   | VPair(v1, v2) ->
       "(" ^ (vtos (v1)) ^ "," ^ (vtos (v2)) ^ ")"
   | VClos _ ->  "fn"
   | VRclos _ -> "fn"
   | VSkip -> "skip")

(* função auxiliar que converte memoria para string *)
      
let rec mtos (mem: mem) : string =
  match mem with
    [] -> ""
  | (y,i) :: tl -> "l" ^ string_of_int y ^ "->" ^ (vtos i) ^ " " ^ (mtos tl)


(**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)

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
  
    (* Asg *)
  | Asg(e1,e2) ->
      (match typeinfer tenv e1 with
         TyRef(t1) -> 
           let t2 = typeinfer tenv e2 in
           if t1 = t2 then TyUnit
           else raise (TypeError "tipos precisam ser iguais para atribuição")
       | _ -> raise (TypeError "tipo da variavel precisa ser ref para ser atribuida"))

    (* Dref *)  
  | Dref(e1) ->
      (match typeinfer tenv e1 with
         TyRef(t1) -> t1
       | _ -> raise (TypeError "tipo da variavel precisa ser ref para ser acessada"))

    (* New *)      
  | New(e1) ->
      (match typeinfer tenv e1 with
         t -> TyRef (t))

    (* Skip *)  
  | Skip -> TyUnit

    (* Whl *)    
  | Whl(e1,e2) -> 
      ( match typeinfer tenv e1 with 
          TyBool -> 
            ( match typeinfer tenv e2 with 
                TyUnit -> TyUnit
              | _ -> raise (TypeError "segundo argumento precisa ser uma expressao do tipo unit"))
        | _ -> raise (TypeError "condição de Whl não é do tipo bool")) 

    (* Seq *)      
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

let rec eval (renv:renv) (e:expr) (mem:mem): v_mem =
  match e with
  
    Num n -> V_Mem(VNum n, mem)
  | True -> V_Mem(VTrue, mem)
  | False -> V_Mem(VFalse, mem)

  | Var x ->
      (match lookup renv x with
         Some v -> V_Mem(v, mem)
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      (match eval renv e1 mem with V_Mem(v1, mem') ->
         match eval renv e2 mem' with V_Mem(v2, mem'') -> 
           V_Mem((compute oper v1 v2), mem''))

  | Pair(e1,e2) ->
      (match eval renv e1 mem with V_Mem(v1, mem') ->
         match eval renv e2 mem' with V_Mem(v2, mem'') -> 
           V_Mem(VPair(v1,v2), mem''))

  | Fst e ->
      (match eval renv e mem with
       | V_Mem(VPair(v1,_), mem') -> V_Mem(v1, mem')
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match eval renv e mem with
       | V_Mem(VPair(_,v2), mem') -> V_Mem(v2, mem')
       | _ -> raise BugTypeInfer)

  | If(e1,e2,e3) ->
      (match eval renv e1 mem with
         V_Mem(VTrue, mem') -> eval renv e2 mem'
       | V_Mem(VFalse, mem') -> eval renv e3 mem'
       | _ -> raise BugTypeInfer )

  | Fn (x,_,e1) -> V_Mem(VClos(x,e1,renv), mem)

  | App(e1,e2) ->
      (match eval renv e1 mem with V_Mem(v1, mem') ->
         (match v1 with 
            VClos(x,ebdy,renv') ->
              (match eval renv' e2 mem' with V_Mem(v2, mem'') ->
                 let renv'' = update renv' x v2
                 in eval renv'' ebdy mem'')

          | VRclos(f,x,ebdy,renv') ->
              (match eval renv' e2 mem' with V_Mem(v2, mem'') ->
                 let renv''  = update renv' x v2 in
                 let renv''' = update renv'' f v1
                 in eval renv''' ebdy mem'')
          | _ -> raise BugTypeInfer))

  | Let(x,_,e1,e2) ->
      (match eval renv e1 mem with V_Mem(v1, mem') ->
         let renv' = update renv x v1 in
         eval renv' e2 mem')

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2 mem
        
  | LetRec _ -> raise BugParser

  | Seq(e1, e2) ->
      (match eval renv e1 mem with 
         V_Mem(VSkip, mem') ->
           eval renv e2 mem'
       | _ -> raise BugTypeInfer) 
        
  | Whl(e1,e2) -> 
      let e3 = If(e1, Seq(e2,Whl(e1,e2)), Skip) in
      eval renv e3 mem
  
  | Asg(e1,e2) ->
      (match eval renv e1 mem with 
         V_Mem(Vl l, mem') ->
           (match eval renv e2 mem' with
              V_Mem(v, mem'') ->
                V_Mem(VSkip, update_mem mem'' l v))
       | _ -> raise BugTypeInfer)
      
  | Skip -> V_Mem(VSkip, mem)
              
  | Dref(e1) ->
      (match eval renv e1 mem with 
         V_Mem(Vl l, mem') ->
           V_Mem(lookup_mem mem' l, mem')
       | _ -> raise BugTypeInfer)
      
  | New(e1) -> 
      (match eval renv e1 mem with 
         V_Mem(l, mem') ->
           (alloc_mem mem' l))

                     
(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v_mem = eval [] e [] in
    match v_mem with
    | V_Mem(v, mem) ->
        let v_str = vtos v in
        let mem_str = mtos mem in
        print_string (v_str ^ " : " ^ ttos t ^ " - mem: " ^ mem_str)
  with
  | TypeError msg -> print_string ("erro de tipo - " ^ msg)

   
 (* as exceções abaixo nao podem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"
                        

 (* +++++++++++++++++++++++++++++++++++++++*)
 (*                TESTES                  *)
 (*++++++++++++++++++++++++++++++++++++++++*)


let e'' = Let("x", TyInt, Num 5, App(Var "foo", Num 10))

let e'  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e'')

let tst = Let("x", TyInt, Num(2), e') 
    
let meu_tst = Let("x", TyRef TyInt, New (Num 3), Skip)
    
let teste1 = Let("x", TyRef TyInt, New (Num 3),
                 Let("y", TyInt, Dref (Var "x"), 
                     Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)), 
                         Binop(Sum, Var "y",  Dref (Var "x")))))
     
let teste2 = Let("x", TyRef TyInt, New (Num 0),
                 Let("y", TyRef TyInt, Var "x", 
                     Seq(Asg(Var "x", Num 1), 
                         Dref (Var "y"))))
    
let counter1 = Let("counter", TyRef TyInt, New (Num 0),
                   Let("next_val", TyFn(TyUnit, TyInt),
                       Fn("w", TyUnit, 
                          Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                              Dref (Var "counter"))),
                       Binop(Sum, App (Var "next_val", Skip), 
                             App (Var "next_val", Skip))))

let tst_Dref = Dref(New (Num 3))

let e2 = Let("x", TyInt, Num 5, Var "foo")

let e1  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e2)

let tst2 = Let("x", TyInt, Num(2), e1)
  
let testeWhile = Let ("x", TyRef TyInt, New (Num 1), Whl (Binop (Gt, Num 5, Dref (Var "x")), Asg (Var "x", Binop (Sum, Dref (Var "x"), Num 1))))
let tst_seq = Seq(Skip, Num 0)
let whilefat = Whl(Binop(Gt, Dref (Var "z"), Num 0), 
                   Seq( Asg(Var "y", Binop(Mult, Dref (Var "y"), Dref (Var "z"))), 
                        Asg(Var "z", Binop(Sub,  Dref (Var "z"), Num 1)))                       
                  ) 
        
let tst_let = Let("y", 
                  TyRef TyInt, 
                  New (Num 1), 
                  Seq (Skip, Num 0))                       
let tesst =  Asg(Var "y", Binop(Mult, Num 5, Num 5))
let bodyfat = Let("z", 
                  TyRef TyInt, 
                  New (Var "x"),
                  Let("y", 
                      TyRef TyInt, 
                      New (Num 1), 
                      Seq (whilefat, Dref (Var "y"))))
    
let impfat = Let("fat", 
                 TyFn(TyInt,TyInt), 
                 Fn("x", TyInt, bodyfat), 
                 App(Var "fat", Num 5))