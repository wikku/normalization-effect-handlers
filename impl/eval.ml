open Syntax

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
  | Do v -> eval_do (eval v ctx)
  | Handle (e, (x, r, eh, y, er)) ->
    eval_handle
      (eval e ctx)
      (fun v vc -> eval eh ((x,v) :: (r,vc) :: ctx))
      (fun v -> eval er ((y,v) :: ctx))
  | Lift e -> eval_lift (eval e ctx)
