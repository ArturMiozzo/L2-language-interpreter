(*  T ::= int | bool | T1 --> T2 |  T1 * T2  *)

type tipo = 
    TyInt 
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo 
  | TyRef of tipo
  | TyUnit

type ident = string
  
type bop = Sum | Sub | Mult  | Gt | Lt | Geq | Leq | Eq
  
   
   (* e ::= n | x | b | e1 op e2 
          | (e1,e2) | fst e | snd e
          | if e1 then e2 else e3
          | fn x:T => e | e1 e2 | let x:T = e1 in e2
          | let rec f: T1--> T2 = fn x: T1 => e1 in e2 *)
    
type expr  = 
    Num of int  
  | Var of ident 
  | True
  | False
  | Binop of bop * expr * expr
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
              
              
type amb = (ident * tipo) list 
    
type memory = (expr * expr) list
    
type exp_mem = Em of expr * memory
    
let empty_gamma : amb = []
    
let rec lookup (gamma: amb) (x:ident) : tipo option = 
  match gamma with
    []          -> None
  | (y,t) :: tl -> if (y = x) then Some t else lookup tl x
  
let rec update (gamma: amb) (x:ident) (t:tipo) : amb = 
  (x,t) :: gamma 
  
let rec lookupMem (sigma: memory) (x:expr) : expr option = 
  match sigma with
    []          -> None
  | (y,e) :: tl -> if (y = x) then Some e else lookupMem tl x
  
let rec updateMem (sigma: memory) (x:expr) (e:expr) : memory = 
  (x,e) :: sigma
  

(* TypeError é ativada se programador L1 escreveu expressão mal tipada *) 

exception TypeError of string 
                              
(* BugParser ativada se parser deixou passar expressão c/ erro de sintaxe *)

exception BugParser
    
let rec typeinfer (gamma: amb) (e:expr) : tipo  = 
  match e with
  
  | Num _ -> TyInt 
    
  | Var x -> 
      (match lookup gamma x with
         Some t -> t
       | None   -> raise (TypeError ("variavel nao declarada:" ^ x)))
      
  | True  -> TyBool
  | False -> TyBool 
  
    (*  G |-- e1:int    G |-- e2:int     bop in {+,-,*}
       ------------------------------------------------
                 G |-- e1  bop  e2 : int 
                 
       G |-- e1:int    G |-- e2:int     bop in {=, <, >, >=, <=,*}
       ----------------------------------------------------------
                 G |-- e1  bop  e2 : bool
                
*) 
    
  | Binop(oper,e1,e2) -> 
      let t1 = typeinfer gamma e1 in
      let t2 = typeinfer gamma e2 in
      if t1 = TyInt && t2 = TyInt then 
        (match oper with
           Sum | Sub | Mult -> TyInt
         | Eq | Lt | Gt | Geq | Leq -> TyBool) 
      else raise (TypeError "operando nao é do tipo int")
  
      
  | Pair(e1,e2) -> TyPair(typeinfer gamma e1, typeinfer gamma e2) 
  | Fst e1 -> 
      (match typeinfer gamma e1 with
         TyPair(t1,_) -> t1
       | _ -> raise (TypeError "fst espera tipo par"))
  | Snd e1 -> 
      (match typeinfer gamma e1 with
         TyPair(_,t2) -> t2
       | _ -> raise (TypeError "fst espera tipo par"))
    
  | If(e1,e2,e3) -> 
      ( match typeinfer gamma e1 with 
          TyBool -> 
            let t2 = typeinfer gamma e2 in
            let t3 = typeinfer gamma e3
            in if t2 = t3 then t2 
            else raise (TypeError "then e else com tipos diferentes")
        | _ -> raise (TypeError "condição de IF não é do tipo bool")) 
      
  | Fn(x,t,e1) -> 
      let t1 = typeinfer (update gamma x t) e1
      in TyFn(t,t1)
        
  | App(e1,e2) -> 
      (match typeinfer gamma e1 with
         TyFn(t, t') ->  if (typeinfer gamma e2) = t then t' 
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))
           
  | Let(x,t,e1,e2) -> 
      if (typeinfer gamma e1) = t then typeinfer (update gamma x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )
  
          
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) -> 
      let gamma_tf = update gamma f tf in
      let gamma_tf_tx = update gamma_tf x tx in
      if (typeinfer gamma_tf_tx e1) = t2 then typeinfer gamma_tf e2
      else raise (TypeError "tipo da funcao diferente do tipo declarado" )
  
   (* se não colocarmos essa ultimo pattern teremos warning:
      pattern matching non exhaustive *)  

  | LetRec _ -> raise BugParser
  
  | Asg(e1,e2) ->
      (match typeinfer gamma e1 with
         TyRef(t1) -> 
           let t2 = typeinfer gamma e2 in
           if t1 = t2 then TyUnit
           else raise (TypeError "tipos precisam ser iguais para atribuição")
       | _ -> raise (TypeError "tipo da variavel precisa ser ref para ser atribuida"))
  
  | Dref(e1) ->
      (match typeinfer gamma e1 with
         TyRef(t1) -> t1
       | _ -> raise (TypeError "tipo da variavel precisa ser ref para ser acessada"))
      
  | New(e1) ->
      let t1 = typeinfer gamma e1
      in TyRef(t1) 
  
  | Skip -> TyUnit
    
  | Whl(e1,e2) -> 
      ( match typeinfer gamma e1 with 
          TyBool -> 
            ( match typeinfer gamma e2 with 
                TyUnit -> TyUnit
              | _ -> raise (TypeError "segundo argumento precisa ser uma expressao do tipo unit"))
        | _ -> raise (TypeError "condição de Whl não é do tipo bool")) 
      
  | Seq(e1,e2) ->
      (match typeinfer gamma e1 with
         TyUnit -> typeinfer gamma e2
       | _ -> raise (TypeError "primeiro argumento precisa ser uma expressao do tipo unit"))
  

(* função auxiliar que convert tipo para string *)

let rec ttos (t:tipo) : string =
  match t with 
    TyInt  -> "int" 
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")" 
  | TyRef(t1)   ->  "("  ^ (ttos t1) ^ ")"
  | TyUnit -> "unit" 
   
                                                                                                    
   (* ========================================= *)
   (*    Avaliador                              *)
   (* ========================================= *)
                        
              
let rec isvalue (e:expr) : bool  = match e with
    True | False | Num _ | Fn(_,_,_) -> true 
  | Pair(e1,e2) -> isvalue(e1) && isvalue(e2)
  | _ -> false
    
    
let rec subs (v:expr) (x:ident) (e:expr) : expr = 
  let rec sb (e:expr)  = 
    match e with
      Num _ -> e
    | True -> e
    | False -> e
      
    | Binop(op,e1,e2) -> Binop(op, sb e1, sb e2)
    | App(e1,e2) -> App(sb e1, sb e2)
    | Pair(e1,e2) -> Pair(sb e1, sb e2)
    | Fst(e1) -> Fst(sb e1)
    | Snd(e1) -> Snd(sb e1)
    | If(e1,e2,e3) -> If(sb e1,sb e2,sb e3)
                        
    | Fn(y,t,e1) -> if (x = y) then e else Fn(y,t,sb e1)
    | Var y -> if (x = y) then v else e
    | Let(y,t, e1, e2) -> 
        Let(y,t, sb e1,if x = y then e2 else sb e2)
    | LetRec(f,tf,ef,e2) -> 
        if x = f then e 
        else LetRec(f,tf, sb ef, sb e2) 
            
    | Asg(e1,e2) -> Asg(sb e1, sb e2)
    | Dref(e1) -> Dref(sb e1)
    | New(e1) -> New(sb e1)
    | Seq(e1,e2) -> Seq(sb e1,sb e2)
    | Whl(e1,e2) -> Whl(sb e1,sb e2)
    | Skip -> e
      
  in sb e
    
    
exception  NoRuleApplies
  
let compute(oper: bop) (v1: expr) (v2:expr) = match (oper,v1,v2) with
    (Sum, Num(n1),  Num(n2)) -> Num(n1+n2) 
  | (Sub, Num(n1),  Num(n2)) -> Num(n1-n2)
  | (Mult, Num(n1), Num(n2)) -> Num(n1*n2)
  | (Eq, Num(n1), Num(n2)) -> if (n1 = n2) then True else False
  | (Gt, Num(n1), Num(n2)) -> if (n1 > n2) then True else False
  | (Lt, Num(n1), Num(n2)) -> if (n1 < n2) then True else False
  | (Geq, Num(n1), Num(n2)) -> if (n1 >= n2) then True else False
  | (Leq, Num(n1), Num(n2)) -> if (n1 <= n2) then True else False
  | _ -> raise NoRuleApplies
        
    

let rec step (e:expr) (sigma:memory): exp_mem = match e with 
  | Binop(oper, e1,e2) when (isvalue e1) && (isvalue e2) -> 
      Em(compute oper e1 e2, sigma)
  | Binop(oper,v1,e2) when (isvalue v1) ->
      (match step e2 sigma with Em(e2', sigma') -> Em(Binop(oper,v1,e2'), sigma'))
  | Binop(oper,e1,e2)  ->
      (match step e1 sigma with Em(e1', sigma') -> Em(Binop(oper,e1',e2), sigma'))
        
  | Pair(v1,e2) when (isvalue v1) ->
      (match step e2 sigma with Em(e2', sigma') -> Em(Pair(v1,e2'), sigma'))
  | Pair(e1,e2)  ->
      (match step e1 sigma with Em(e1', sigma') -> Em(Pair(e1',e2), sigma'))
        
  | Fst(Pair(v1,v2)) when (isvalue v1) && (isvalue v2) -> 
      Em(v1, sigma)
  | Fst e -> 
      (match step e sigma with Em(e', sigma') -> Em(Fst e', sigma'))
        
  | Snd(Pair(v1,v2)) when (isvalue v1) && (isvalue v2) -> 
      Em(v2, sigma)
  | Snd e -> 
      (match step e sigma with Em(e', sigma') -> Em(Snd e', sigma'))
        
  | If(True,e2,_) ->
      Em(e2, sigma)
  | If(False,_,e3) ->
      Em(e3, sigma)
  | If(e1,e2,e3) -> 
      (match step e1 sigma with Em(e1', sigma') -> Em(If(e1',e2,e3), sigma'))
        
  | App(Fn(x,t,ebdy), v) when isvalue v ->
      Em(subs v x ebdy, sigma)
  | App(v1, e2) when isvalue v1 ->
      (match step e2 sigma with Em(e2', sigma') -> Em(App(v1, e2'), sigma'))
  | App(e1, e2) ->
      (match step e1 sigma with Em(e1', sigma') -> Em(App(e1', e2), sigma'))
        
  | Let(x,t,v1,e2) -> 
      Em(subs v1 x e2, sigma)
  | Let(x,t,e1,e2) -> 
      (match step e1 sigma with Em(e1', sigma') -> Em(Let(x,t,e1',e2), sigma'))
        
  | LetRec(f, (TyFn(t1,t2) as tf), (Fn(x,tx,e1) as ef),e2) -> 
      let alpha = Fn(x,tx, LetRec(f,tf,ef,e1))
      in Em(subs alpha f e2, sigma)
  | LetRec _ -> raise BugParser
                  
  | Asg(l,v) when (match lookupMem sigma l with
        Some e -> true
      | None   -> false) ->
      let sigma_ = updateMem sigma l v in Em(Skip, sigma_)
  | Asg(v,e) when isvalue v ->
      (match step e sigma with Em(e', sigma') -> Em(Asg(v, e'), sigma'))
  | Asg(e1,e2) ->
      (match step e1 sigma with Em(e1', sigma') -> Em(Asg(e1', e2), sigma'))
        
  |  _ -> raise NoRuleApplies
            
exception BugTypeInfer 
  
let rec evalst (e:expr) (sigma:memory): exp_mem =
  try
    match step e sigma with Em(e', sigma') -> evalst e' sigma'
  with 
    NoRuleApplies -> if isvalue e then Em(e, sigma) else raise BugTypeInfer
          
let rec vtos (v:expr) : string = match v with
    Num n1 -> string_of_int n1
  | True -> "true"
  | False -> "false"
  | Pair(v1,v2) when (isvalue v1) && (isvalue v2) ->
      "(" ^ (vtos v1) ^ "," ^ (vtos v2) ^ ")"
  | Fn _ -> "<fn>"
  | _ ->  raise (Invalid_argument "not a vlue")
            
            
let int_st (e:expr) (sigma:memory) = 
  try
    let t = typeinfer empty_gamma e in
    match evalst e sigma with Em(v, sigma) -> print_string ((vtos v) ^ " : " ^ (ttos t))
  with 
    TypeError msg -> print_string ("erro de tipo: " ^ msg)
      
  | BugParser -> print_string "corrigir bug no typeinfer"
  | BugTypeInfer ->  print_string "corrigir bug do parser para let rec" 
  
        
        
        
        
        
  

(* testes *)             

let upd1 = update empty_gamma "x" TyInt 
let upd2 = update upd1 "f" TyBool 
let upd3 = update upd2 "x" TyBool
  
let testeif = If(Fst (Num 5), Num 10, Num 20)
let testeop = Binop(Mult, True, Num 5)
let teste = Binop(Mult, Var "x" , Num 5)
  


(*   com acúcar sintático:

   let rec pow (x:int) (y:int) : int = 
                  if y = 0 then 1 else x * (pow x (y-1))  
   in (pow 3) 4 
     
     sem açucar sintático:

  let rec pow: int -> (int --> int) = 
    fn x:int => (fn y:int => if y = 0 then 1 else x * (pow x (y-1)) ) 
  in (pow 3) 4 

*)          

let ys1 = Binop(Sub, Var "y", Num 1)     (* y - 1  *)
  
let powapp  =   App(App(Var "pow", Var "x"), ys1)   (* pow *)
                                           
let xp =   Binop(Mult, Var "x", powapp)
      
    (* fn y:int => if y=0 then 1 else x * (pow x (y-1))    *) 
let ebdy = Fn("y",TyInt,If(Binop(Eq, Var "y", Num 0) , Num 1, xp))  
  
let pw = 
  LetRec("pow", TyFn(TyInt, TyFn(TyInt,TyInt)), (* pow: int --> int --> int*)
         Fn("x", TyInt, ebdy), (* fn x: int => ebdy  *)
         App(App(Var "pow", Num 3), Num 4)) (* in  (pow 3) 4    *)
                                            
                                            
    (* l
   
   let rec pow2: int -> (int --> int) = 
       fn x:int => (fn y:int => if y = 0 then 1 else x * (pow x (y-1)) ) 
     in pow 
*)
                                            
let pw2 = 
  LetRec("pow", TyFn(TyInt, TyFn(TyInt,TyInt)), (* pow: int --> int --> int*)
         Fn("x", TyInt, ebdy), (* fn x: int => ebdy  *)
         Var "pow") (* in  pow  *) 
  
