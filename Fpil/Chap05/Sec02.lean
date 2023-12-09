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

def applyPrimE : Arith → Int → Int → Except String Int
  | Arith.plus , x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div  , x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zeor"
    else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrimE p v1 v2

#eval evaluateExcept twoPlusThree
#eval evaluateExcept fourteenDivided


def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus,  x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div,   x, y =>
    if y == 0 then
      none
    else pure (x / y)

def applyPrimExcept := applyPrimE

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2

#eval evaluateM applyPrimOption twoPlusThree
#eval evaluateM applyPrimOption fourteenDivided

#eval evaluateM applyPrimExcept twoPlusThree
#eval evaluateM applyPrimExcept fourteenDivided


def applyDivOption (x : Int) (y : Int) : Option Int :=
  if y == 0 then
    none
  else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
  if y == 0 then
    Except.error s!"Tried to divide {x} by zero"
  else pure (x / y)

def applyPrim' [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus,  x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div,   x, y => applyDiv x y

def evaluateM' [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM' applyDiv e1 >>= fun v1 =>
    evaluateM' applyDiv e2 >>= fun v2 =>
    applyPrim' applyDiv p v1 v2

#eval evaluateM' applyDivOption twoPlusThree
#eval evaluateM' applyDivOption fourteenDivided

#eval evaluateM' applyDivExcept twoPlusThree
#eval evaluateM' applyDivExcept fourteenDivided

-- # Further Effects

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special
deriving Repr

inductive CanFail where
  | div
deriving Repr

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)


def applyPrim'' [Monad m] (applySpecial : special → Int → Int → m Int) :
  Prim special → Int → Int → m Int
  | Prim.plus,  x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM'' [Monad m] (applySpecial : special → Int → Int → m Int) :
  Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM'' applySpecial e1 >>= fun v1 =>
    evaluateM'' applySpecial e2 >>= fun v2 =>
    applyPrim'' applySpecial p v1 v2

open Expr Prim in
def twoPlusThree'' : Expr (Prim CanFail):=
  prim plus (const 2) (const 3)

open Expr Prim CanFail in
def fourteenDivided'' : Expr (Prim CanFail) :=
  prim (other div) (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

#eval evaluateM'' divOption twoPlusThree''
#eval evaluateM'' divOption fourteenDivided''

#eval evaluateM'' divExcept twoPlusThree''
#eval evaluateM'' divExcept fourteenDivided''

-- # No Effects

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM'' (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

-- # Nondeterministic Search

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union $
        addsTo (goal - x) xs >>= fun answer =>
        pure $ x :: answer

#eval Many.take 3 $ addsTo 15 [3, 1, 4, 1, 5, 9, 2, 6]
#eval Many.takeAll $ addsTo 15 [3, 1, 4, 1, 5, 9, 2, 6]
#eval Many.takeAll $ addsTo 15 [18, 2, 3, 1, 4, 16, 5, 9]


inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

open Expr Prim NeedsSearch

#eval Many.takeAll $ evaluateM'' applySearch (prim plus (const 1) (prim (other choose) (const 2) (const 5)))
#eval Many.takeAll $ evaluateM'' applySearch (prim plus (const 1) (prim (other div) (const 2) (const 0)))
#eval (evaluateM'' applySearch (prim (other div) (const 90) (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll

-- # Custom Enviroments

def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure $ f x y

open Expr Prim in
#eval evaluateM'' applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) $ exampleEnv

-- Exercises
