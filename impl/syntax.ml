open Format

type info = Lexing.position * Lexing.position

let rec iter f n x = if n = 0 then x else iter f (n-1) (f x)

let assoc, deassoc = List.assoc, List.remove_assoc

type name = string

type kind = T | E | R

type ty =
  | TVar of name
  | TArr of ty * ro * ty
  | TForall of name * kind * ty
and ef =
  | EVar of name
  | Op of (name * kind) list * ty * ty
and ro =
  | RVar of name
  | RRow of ef list

type typelike = Ty of ty | Ef of ef | Ro of ro

type value =
  | Var of name
  | Lam of name * exp
and exp =
  | Var of name
  | Lam of name * exp
  | App of exp * exp
  | Do of value
  | Handle of exp * handler
  | Lift of exp
and handler = name * name * exp * name * exp



type command =
  | Typ of exp

let eov : value -> exp = function
  | Var x -> Var x
  | Lam (x, e) -> Lam (x, e)

let voe : exp -> value = function
  | Var x -> Var x
  | Lam (x, e) -> Lam (x, e)
  | _ -> failwith "not a value"

let rec pr_exp0 ppf = function
  | Lift e -> fprintf ppf "[%a]" pr_exp0 e
  | Var s -> fprintf ppf "%a" pp_print_string s
  | Lam _ as lam -> fprintf ppf "@[<1>(%a)@]" pr_lambda lam
  | Do v -> fprintf ppf "do (%a)" pr_lambda (eov v)
  | Handle (e, h) -> fprintf ppf "@[handle@ @[%a@]@ @[%a@]@]" pr_exp0 e pr_handler h
  | App _ as app -> pr_app ppf app
and pr_handler ppf (x, r, eh, y, er) =
  fprintf ppf "{%s, %s. %a;@ %s. %a}"
    x r pr_exp0 eh y pr_exp0 er
and pr_app ppf e =
  fprintf ppf "@[<2>%a@]" pr_other_applications e
and pr_other_applications ppf f =
  match f with
  | App (f, arg) -> fprintf ppf "%a@ %a" pr_app f pr_exp0 arg
  | f -> pr_exp0 ppf f
and pr_lambda ppf = function
  | Lam (s, lam) ->
     fprintf ppf "@[<1>%s%a%s@ %a@]" "\\" pp_print_string s "." pr_lambda lam
  | e -> pr_app ppf e

let rec subst s : exp -> exp = function
  | Var(x) as e -> (try assoc x s with Not_found -> e)
  | Lam(x,t) -> Lam(x, subst (deassoc x s) t)
  | App(t1,t2) -> App(subst s t1, subst s t2)
  | Lift(t) -> Lift(subst s t)
  | Do(t) -> Do(voe @@ subst s @@ eov t)
  | Handle(t1,(x,r,t2,y,t3)) ->
    Handle(subst s t1,
            (x, r, subst (deassoc x (deassoc r s)) t2,
             y, subst (deassoc y s) t3))

(*
let exp_info t = match t with
  | Var(fi,_)
  | Lam(fi,_,_)
  | App(fi,_,_)
  | Lift(fi,_)
  | Do(fi,_)
  | Handle(fi,_,_) -> fi
*)

type frame =
  | FArg of exp
  | FFun of value
  | FLift
  | FHandle of handler

type econt = frame list

type redex =
  | RBeta of name * exp * value
  | RLift of value
  | RReturn of value * handler
  | RDo of econt * value * handler

let ffree n = function
  | FArg _ | FFun _ -> n
  | FLift -> n + 1
  | FHandle _ -> if n > 0 then n - 1 else failwith "nonfree"

let free e = List.fold_left ffree 0 e

let rec find_handler n rev_res = function
  | FHandle h :: fs when n = 0 -> (List.rev rev_res, h, fs)
  | f :: fs -> find_handler (ffree n f) (f :: rev_res) fs
  | [] -> failwith "handler not found"

let rec find_redex k = function
  | App ((Lam (x1, e1)), (Lam _ as v)) -> RBeta (x1, e1, voe v), k
  | App (Lam _ as l, e2) -> find_redex (FFun (voe l) :: k) e2
  | App (e1, e2) -> find_redex (FArg e2 :: k) e1
  | Lift (Lam _ as l) -> RLift (voe l), k
  | Lift e -> find_redex (FLift :: k) (e :> exp)
  | Lam _ | Var _ -> failwith "no redex"
  | Do (Lam _ as l) ->
    let r, h, k = find_handler 0 [] k in (RDo (r, l, h)), k
  | Do _ -> failwith "Do nonval"
  | Handle (Lam _ as v, h) -> RReturn (voe v, h), k
  | Handle (e, h) -> find_redex (FHandle h :: k) e

let frame e : frame -> exp = function
  | FArg e' -> App (e, e')
  | FFun l -> App (eov l, e)
  | FLift -> Lift e
  | FHandle h -> Handle (e, h)

let plug e k = List.fold_left frame e k

let reduce = function
  | RBeta (x, e, v) -> subst [x, eov v] e
  | RLift v -> eov v
  | RReturn (v, (_, _, _, x, e)) -> subst [x, eov v] e
  | RDo (k, v, ((x, r, e, _, _) as h)) ->
    subst [x, eov v; r, Lam ("z", Handle (plug (Var "z") k, h))] e

let step e =
  match find_redex [] e with
  | r, k -> plug (reduce r) k
  | exception _ -> failwith "no step"

(***)

let church n =
  let rec aux n exp = if n = 0 then exp else App (Var "f", aux (n-1) exp) in
  Lam ("f", (Lam ("x", aux n (Var "x"))))

let tick = Lam ("x", Lift (Do (Var "x")))
let id = Lam ("x", Var "x")
let fig31 = App (App (Do id, eov tick), eov id)
let reader n = ("x", "r", App (eov @@ Var "r", eov @@ church n), "x", eov @@ Var "x")
let id_handler = ("x", "r", App (eov @@ Var "r", eov @@ Var "x"), "x", eov @@ Var "x")
let fig31' = Handle (Handle (fig31, reader 5), id_handler)

(***)

type goodval = Fun of (goodval -> goodexp)
and goodexp =
  | Val of goodval
  | Stk of goodval * int * (goodval -> goodexp)


let eval_lam f = Val (Fun f)

let rec eval_lift = function
  | Val v -> Val v
  | Stk (v, n, k) -> Stk (v, n+1, fun u -> eval_lift (k u))

let rec eval_app e1 e2 =
  match e1 with
  | Stk (v, n, k) -> Stk (v, n, fun u -> eval_app (k u) e2)
  | Val f ->
  match e2 with
  | Stk (v, n, k) -> Stk (v, n, fun u -> eval_app e1 (k u))
  | Val v ->
  match f with Fun f -> f v

let rec eval_handle e eh er =
  match e with
  | Val v -> er v
  | Stk (v, n, k) ->
    if n = 0
    then eh v (Fun (fun u -> eval_handle (k u) eh er))
    else Stk (v, n-1, fun u -> eval_handle (k u) eh er)

let eval_do = function
  | Val v -> Stk (v, 0, fun u -> Val v)
  | _ -> failwith "do nonval"

let rec eval (e : exp) ctx : goodexp = match e with
  | App (e1, e2) -> eval_app (eval e1 ctx) (eval e2 ctx)
  | Var x -> Val (assoc x ctx)
  | Lam (x, e) -> eval_lam (fun v -> eval e ((x,v) :: ctx))
  | Do v -> eval_do (eval (eov v) ctx)
  | Handle (e, (x, r, eh, y, er)) ->
    eval_handle
      (eval e ctx)
      (fun v vc -> eval eh ((x,v) :: (r,vc) :: ctx))
      (fun v -> eval er ((y,v) :: ctx))
  | Lift e -> eval_lift (eval e ctx)

let rec reify = function
  | Val v -> 
  | Stk (v, _, k) ->

