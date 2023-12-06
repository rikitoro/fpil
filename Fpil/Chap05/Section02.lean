-- # Example : Arithmetic in Monads

-- # Arithmetic Expressions

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim  : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

-- # Evaluating Expressions

-- def evaluateOption : Expr Arith → Option Int
--   | Expr.const i => pure i
--   | Expr.prim p e1 e2 =>
--     evaluateOption e1 >>= fun v1 =>
--     evaluateOption e2 >>= fun v2 =>
--     match p with
--     | Arith.plus => pure (v1 + v2)
--     | Arith.minus => pure (v1 - v2)
--     | Arith.times => pure (v1 * v2)
--     | Arith.div => if v2 == 0 then none else pure (v1 / v2)

-- #eval evaluateOption twoPlusThree
-- #eval evaluateOption fourteenDivided

def applyPrim : Arith → Int → Int → Option Int
  | Arith.plus , x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div  , x, y => if y == 0 then none else pure (x / y)

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrim p v1 v2

#eval evaluateOption twoPlusThree
#eval evaluateOption fourteenDivided
