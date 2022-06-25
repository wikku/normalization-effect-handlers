open Syntax

type frame =
  | FArg of exp
  | FFun of exp
  | FLift
  | FHandle of handler

type econt = frame list

let frame e : frame -> exp = function
  | FArg e' -> App (e, e')
  | FFun l -> App (l, e)
  | FLift -> Lift e
  | FHandle h -> Handle (e, h)

let plug e k = List.fold_left frame e k

let ffree n = function
  | FArg _ | FFun _ -> n
  | FLift -> n+1
  | FHandle _ -> if n > 0 then n-1 else failwith "nonfree"

let free e = List.fold_left ffree 0 e

type redex =
  | RBeta of string * exp * exp
  | RLift of exp
  | RReturn of exp * handler
  | RDo of econt * exp * handler

let rec find_handler n rev_res = function
  | FHandle h :: fs when n = 0 -> (List.rev rev_res, h, fs)
  | f :: fs -> find_handler (ffree n f) (f :: rev_res) fs
  | [] -> failwith "handler not found"

let rec decomp k = function
  | App (e1, e2) when is_value e1 && is_value e2 ->
    (match e1 with
    | Lam (x, e1) -> RBeta (x, e1, e2), k
    | _ -> failwith "app nonvalue")
  | App (e1, e2) when is_value e1 -> decomp (FFun e1 :: k) e2
  | App (e1, e2) -> decomp (FArg e2 :: k) e1
  | Lift e when is_value e -> RLift e, k
  | Lift e -> decomp (FLift :: k) e
  | Do v -> let r, h, k = find_handler 0 [] k in (RDo (r, v, h)), k
  | Handle (e, h) when is_value e -> RReturn (e, h), k
  | Handle (e, h) -> decomp (FHandle h :: k) e
  | Lam _ | Var _ -> failwith "no redex"


let contract = function
  | RBeta (x, e, v) -> subst [x, v] e
  | RLift v -> v
  | RReturn (v, (_, _, _, x, e)) -> subst [x, v] e
  | RDo (k, v, ((x, r, e, _, _) as h)) ->
    subst [x, v; r, Lam ("z", Handle (plug (Var "z") k, h))] e

let step e =
  match decomp [] e with
  | r, k -> plug (contract r) k
  | exception _ -> failwith "no step"

let rec multistep e =
  match step e with
  | e' -> multistep e'
  | exception _ -> e
