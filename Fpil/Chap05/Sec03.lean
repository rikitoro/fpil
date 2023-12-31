import Fpil.Util.BinTree
import Fpil.Util.State

-- # do-Notation for Monads

-- do E
--> E

#eval do Option.some 1
#eval do [1, 2, 3]
-- #eval do 1

-- do let ← E1
--    Stmt
--    ...
--    En
-->
-- E1 >>= fun x =>
-- do Stmt
--    ...
--    En

-- do E1
--    Stmt
--    ...
--    En
-->
-- E1 >>= fun () =>
-- do Stmt
--    ...
--    En

-- do let x := E1
--    Stmt
--    ...
--    En
-->
-- let x := E1
-- do Stmt
--    ...
--    En

def firstThirdFifthSeventh [Monad m]
  (lookup : List α → Nat → m α) (xs : List α) :
  m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

#eval firstThirdFifthSeventh List.get? [1, 2, 3, 4, 5]
#eval firstThirdFifthSeventh List.get? [1, 2, 3, 4, 5, 6, 7, 8]

open State in
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α -> State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch l x r => do
      let numberedl ← helper l
      let n ← get
      set (n + 1)
      let numberedr ← helper r
      pure (BinTree.branch numberedl (n, x) numberedr)
  (helper t 0).snd

open BinTree in
def btree1 : BinTree String :=
  branch
    (branch leaf "A" leaf)
    "B"
    (branch
      (branch leaf "C" leaf)
      "D"
      (branch leaf "E" leaf)
    )

#eval number btree1

def mapM [Monad m] (f : α → m β) :
  List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure $ (← f x) :: (← mapM f xs)

open State in
def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

open State in
def number' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper :
    BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch l x r => do
      pure $
        BinTree.branch
          (← helper l) (← increment, x) (← helper r)
  (helper t 0).snd

#eval number' btree1

-- # Exercise
