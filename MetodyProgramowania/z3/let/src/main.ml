open Ast

let parse (s : string) : expr =
  Parser.main Lexer.read (Lexing.from_string s)

module M = Map.Make(String)

type env = string M.t

type value =
  | VInt of int
  | VBool of bool

let eval_op (op : bop) (val1 : value) (val2 : value) : value =
  match op, val1, val2 with
  | Add,  VInt  v1, VInt  v2 -> VInt  (v1 + v2)
  | Sub,  VInt  v1, VInt  v2 -> VInt  (v1 - v2)
  | Mult, VInt  v1, VInt  v2 -> VInt  (v1 * v2)
  | Div,  VInt  v1, VInt  v2 -> VInt  (v1 / v2)
  | And,  VBool v1, VBool v2 -> VBool (v1 && v2)
  | Or,   VBool v1, VBool v2 -> VBool (v1 || v2)
  | Leq,  VInt  v1, VInt  v2 -> VBool (v1 <= v2)
  | Eq,   _,        _        -> VBool (val1 = val2)
  | _,    _,        _        -> failwith "type error"

let rec subst (x : ident) (s : expr) (e : expr) : expr =
  match e with
  | Binop (op, e1, e2) -> Binop (op, subst x s e1, subst x s e2)
  | If (b, t, e) -> If (subst x s b, subst x s t, subst x s e)
  | Var y -> if x = y then s else e
  | Let (y, e1, e2) ->
      Let (y, subst x s e1, if x = y then e2 else subst x s e2)
  | _ -> e

let reify (v : value) : expr =
  match v with
  | VInt a -> Int a
  | VBool b -> Bool b

let rec eval (e : expr) : value =
  match e with
  | Int i -> VInt i
  | Bool b -> VBool b
  | Binop (op, e1, e2) ->
      eval_op op (eval e1) (eval e2)
  | If (b, t, e) ->
      (match eval b with
           | VBool true -> eval t
           | VBool false -> eval e
           | _ -> failwith "type error")
  | Let (x, e1, e2) ->
      eval (subst x (reify (eval e1)) e2)
  | Var x -> failwith ("unknown var " ^ x)
  
let rec cp (e : expr) : expr =
  match e with
  | Int i -> Int i
  | Bool b -> Bool b
  | Binop (op, e1, e2) -> (match cp e1, cp e2 with
    | Int i1, Int i2 -> reify (eval (Binop (op, Int i1, Int i2)))
    | Bool b1, Bool b2 -> reify (eval (Binop (op, Bool b1, Bool b2)))
    | u1, u2 -> Binop (op, u1, u2))
  | If (e1, e2, e3) -> (match cp e1, cp e2, cp e3 with
    | Bool b1, p2, p3 -> if b1 then p2 else p3
    | p1, p2, p3 -> If (p1, p2, p3))
  | Let (x, e1, e2) -> (match cp e1 with
    | Int i1 -> cp (subst x (Int i1) e2)
    | Bool b1 -> cp (subst x (Bool b1) e2)
    | u1 -> Let (x, u1, cp e2))
  | Var x -> Var x


let alpha_equiv (e1 : expr) (e2 : expr) : bool =
  let rec f (e1 : expr) (e2 : expr) (en1 : env) (en2 : env) : bool = match e1, e2 with
    | Int i, Int i' -> i = i'
    | Bool b, Bool b' -> b = b'
    | Binop (op, e1, e2), Binop (op', e1', e2') -> op = op' && f e1 e1' en1 en2 && f e2 e2' en1 en2
    | If (e1, e2, e3), If (e1', e2', e3') -> f e1 e1' en1 en2 && f e2 e2' en1 en2 && f e3 e3' en1 en2
    | Let (x, e1, e2), Let (x', e1', e2') -> f e1 e1' en1 en2 && f e2 e2' (M.add x x' en1) (M.add x' x en2)
    | Var x, Var x' -> (match M.find_opt x en1, M.find_opt x' en2 with
      | Some a1, Some a2 -> a1 = x' && x = a2
      | _ -> false)
    | _ -> false
  in f e1 e2 M.empty M.empty

let rename_expr (e : expr) : expr =
  let rec f (e : expr) (en : env) (t : string) : expr = match e with
    | Int i -> Int i
    | Bool b -> Bool b
    | Binop (op, e1, e2) -> Binop(op, f e1 en (t^"0"), f e2 en (t^"1"))
    | If (e1, e2, e3) -> If(f e1 en (t^"2"), f e2 en (t^"0"), f e3 en (t^"1"))
    | Let (x, e1, e2) -> Let (t, f e1 en (t^"0"), f e2 (M.add x t en) (t^"1"))
    | Var x -> (match M.find_opt x en with
      | Some y -> Var y
      | None -> Var x)
  in f e M.empty "#"

let interp (s : string) : value =
  eval (parse s)
