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
  | VVar of name
  | VLam of name * exp
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

let is_value = function
  | Var _ | Lam _ -> true
  | App _ | Do _ | Handle _ | Lift _ -> false

let eov : value -> exp = function
  | VVar x -> Var x
  | VLam (x, e) -> Lam (x, e)

let voe : exp -> value = function
  | Var x -> VVar x
  | Lam (x, e) -> VLam (x, e)
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
  | Var x as e -> (try assoc x s with Not_found -> e)
  | Lam (x,t) -> Lam(x, subst (deassoc x s) t)
  | App (t1,t2) -> App(subst s t1, subst s t2)
  | Lift t -> Lift(subst s t)
  | Do t -> Do(voe @@ subst s @@ eov t)
  | Handle (t1,(x,r,t2,y,t3)) ->
    Handle (subst s t1,
            (x, r, subst (deassoc x (deassoc r s)) t2,
             y, subst (deassoc y s) t3))

type frame =
  | FArg of exp
  | FFun of value
  | FLift
  | FHandle of handler

type econt = frame list

let frame e : frame -> exp = function
  | FArg e' -> App (e, e')
  | FFun l -> App (eov l, e)
  | FLift -> Lift e
  | FHandle h -> Handle (e, h)

let plug e k = List.fold_left frame e k

let ffree n = function
  | FArg _ | FFun _ -> n
  | FLift -> n+1
  | FHandle _ -> if n > 0 then n-1 else failwith "nonfree"

let free e = List.fold_left ffree 0 e

type redex =
  | RBeta of name * exp * value
  | RLift of value
  | RReturn of value * handler
  | RDo of econt * value * handler


let rec find_handler n rev_res = function
  | FHandle h :: fs when n = 0 -> (List.rev rev_res, h, fs)
  | f :: fs -> find_handler (ffree n f) (f :: rev_res) fs
  | [] -> failwith "handler not found"

let rec decomp k = function
  | App (e1, e2) when is_value e1 && is_value e2 ->
    (match e1 with
    | Lam (x, e1) -> RBeta (x, e1, voe e2), k
    | _ -> failwith "app nonvalue")
  | App (e1, e2) when is_value e1 -> decomp (FFun (voe e1) :: k) e2
  | App (e1, e2) -> decomp (FArg e2 :: k) e1
  | Lift e when is_value e -> RLift (voe e), k
  | Lift e -> decomp (FLift :: k) e
  | Do v -> let r, h, k = find_handler 0 [] k in (RDo (r, v, h)), k
  | Handle (e, h) when is_value e -> RReturn (voe e, h), k
  | Handle (e, h) -> decomp (FHandle h :: k) e
  | Lam _ | Var _ -> failwith "no redex"


let reduce = function
  | RBeta (x, e, v) -> subst [x, eov v] e
  | RLift v -> eov v
  | RReturn (v, (_, _, _, x, e)) -> subst [x, eov v] e
  | RDo (k, v, ((x, r, e, _, _) as h)) ->
    subst [x, eov v; r, Lam ("z", Handle (plug (Var "z") k, h))] e

let step e =
  match decomp [] e with
  | r, k -> plug (reduce r) k
  | exception _ -> failwith "no step"

let rec multistep e =
  match step e with
  | e' -> multistep e'
  | exception _ -> e

(***)

let church n : value =
  let rec aux n exp = if n = 0 then exp else App (Var "f", aux (n-1) exp) in
  VLam ("f", (Lam ("x", aux n (Var "x"))))

let tick = VLam ("x", Lift (Do (VVar "x")))
let id = VLam ("x", Var "x")
let fig31 = App (App (Do id, eov tick), eov id)
let reader n = ("x", "r", App (eov @@ VVar "r", eov @@ church n), "x", eov @@ VVar "x")
let id_handler = ("x", "r", App (eov @@ VVar "r", eov @@ VVar "x"), "x", eov @@ VVar "x")
let fig31' = Handle (Handle (fig31, reader 5), id_handler)

let w = VLam ("x", App (Var "x", Var "x"))
let ww = App (eov w, eov w)

let stk_ww = App (Do id, ww)
let stk_ww' = Handle (stk_ww, ("_", "_", eov id, "y", Var "y"))

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


(*
let gensym =
  let n = ref 0 in
  (fun () -> incr n; "x" ^ string_of_int (!n))

let rec reify = function
  | Val (Neut x) -> Var x
  | Val (Fun f) -> let x = gensym() in Lam (x, reify (f (Neut x)))
  | Stk (v, n, k) ->
    let Lam (x, e) = reify (Val (Fun k)) in
    subst [x, Do (voe (reify (Val v)))] e
*)
