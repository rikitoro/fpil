import Fpil.Chap04.Sec05


-- # Monads

-- # Checking for none : Don't Repeat Yourself

def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird' (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

#eval firstThird' [1, 2, 3, 4, 5]
#eval firstThird' [1, 2]
#eval firstThird' ([] : List Nat)

-- # Infix Operator

infixl:55 " ~~> " => andThen

def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

#eval firstThirdInfix [1, 2, 3, 4, 5]
#eval firstThirdInfix [1, 2]
#eval firstThirdInfix ([] : List Nat)

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

#eval firstThirdFifthSeventh [1, 2, 3, 4, 5, 6, 7, 8]
#eval firstThirdFifthSeventh [1, 2, 3, 4]

-- # Logging

def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)

#eval sumAndFindEvens [3, 1, 4, 1, 5, 9, 2]

def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

def bTree4 : BinTree Int :=
  BinTree.branch (BinTree.branch BinTree.leaf 2 BinTree.leaf) 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf)

#eval inorderSum bTree4

def sumAndFindEvens' : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens' is
    let (evenHere, ())  := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)

#eval sumAndFindEvens' [3, 1, 4, 1, 5, 9, 2]


structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThen' (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β) : WithLog α β :=
  {log := [], val := x}

def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen'

def sumAndFindEvens'' : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvens'' is ~~> fun sum =>
    ok (i + sum)

deriving instance Repr for WithLog

#eval sumAndFindEvens'' [3, 1, 4, 1, 5, 9, 2, 6]

def inorderSum'' : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum'' l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum'' r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)

#eval inorderSum'' bTree4
