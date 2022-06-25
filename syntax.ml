let assoc, deassoc = List.assoc, List.remove_assoc

type exp =
  | Var of string
  | Lam of string * exp
  | App of exp * exp
  | Do of exp
  | Handle of exp * handler
  | Lift of exp
and handler = string * string * exp * string * exp

let is_value = function
  | Var _ | Lam _ -> true
  | App _ | Do _ | Handle _ | Lift _ -> false

let rec subst s : exp -> exp = function
  | Var x as e -> (try assoc x s with Not_found -> e)
  | Lam (x,t) -> Lam(x, subst (deassoc x s) t)
  | App (t1,t2) -> App(subst s t1, subst s t2)
  | Lift t -> Lift(subst s t)
  | Do t -> Do(subst s t)
  | Handle (t1,(x,r,t2,y,t3)) ->
    Handle (subst s t1,
            (x, r, subst (deassoc x (deassoc r s)) t2,
             y, subst (deassoc y s) t3))

(***)

let rec iter f n x = if n = 0 then x else iter f (n-1) (f x)

open Format

let rec pr_exp0 ppf = function
  | Lift e -> fprintf ppf "[%a]" pr_exp0 e
  | Var s -> fprintf ppf "%a" pp_print_string s
  | Lam _ as lam -> fprintf ppf "@[<1>(%a)@]" pr_lambda lam
  | Do v -> fprintf ppf "do (%a)" pr_lambda v
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

let church n : exp =
  let rec aux n exp = if n = 0 then exp else App (Var "f", aux (n-1) exp) in
  Lam ("f", (Lam ("x", aux n (Var "x"))))

let tick = Lam ("x", Lift (Do (Var "x")))
let id = Lam ("x", Var "x")
let fig31 = App (App (Do id, tick), id)
let reader n = ("x", "r", App (Var "r", church n), "x", Var "x")
let id_handler = ("x", "r", App (Var "r", Var "x"), "x", Var "x")
let fig31' = Handle (Handle (fig31, reader 5), id_handler)

let w = Lam ("x", App (Var "x", Var "x"))
let ww = App (w, w)

let stk_ww = App (Do id, ww)
let stk_ww' = Handle (stk_ww, ("_", "_", id, "y", Var "y"))
