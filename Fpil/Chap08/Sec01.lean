-- # Programming with Dependent Types

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

#eval natOrStringThree true
#eval natOrStringThree false

-- # Indexed Families

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- example : Vect String 3 := Vect.nil
-- type mismatch
--   Vect.nil
-- has type
--   Vect String 0 : Type
-- but is expected to have type
--   Vect String 3 : Type

example : Vect String 0 := Vect.nil

-- example : Vect String n := Vect.nil

example : Vect String 2 := Vect.cons "Hello" $ Vect.cons "world" Vect.nil
-- example : Vect String n := Vect.cons "Hello" $ Vect.cons "world" Vect.nil

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x $ replicate k x

-- def Vect.replicate' (n : Nat) (x : α) : Vect α n :=
--   match n with
--   | 0 => .nil
--   | k + 1 => .cons x $ .cons x $ replicate' k x
--
-- application type mismatch
--   cons x (cons x (replicate' k x))
-- argument
--   cons x (replicate' k x)
-- has type
--   Vect α (k + 1) : Type ?u.6618
-- but is expected to have type
--   Vect α k : Type ?u.6618

#eval ["Nount Hood", "Mount Jefferson", "South Sister"].zip
  ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]

#eval [3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]


def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) $ zip xs ys

-- def List.zip' : List α → List β → List (α × β)
--   | [], [] => []
--   | x :: xs, y :: ys => (x, y) :: zip' xs ys
--
-- missing cases:
-- (cons _ _), []
-- [], (cons _ _)

-- def Vect.zip' : Vect α n → Vect β n → Vect (α × β) n
--   | .nil, .nil => .nil
--   | .nil, .cons y ys => .nil
--   | .cons x xs, .cons y ys => .cons (x, y) $ zip' xs ys
-- --
-- type mismatch
--   cons y ys
-- has type
--   Vect β (?m.14415 + 1) : Type ?u.14227
-- but is expected to have type
--   Vect β 0 : Type ?u.14227

def Vect.zip_ : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) $ zip_ k xs ys

-- ## Exercises

-- ### Vect.zip

deriving instance Repr for Vect

def oregonianPeaks : Vect String 3 :=
  .cons "Nount Hood" <| .cons "Mount Jefferson" <| .cons "South Sister" .nil

def danishPeaks :=
  Vect.cons "Møllehøj" <| .cons "Yding Skovhøj" <| .cons "Ejer Bavnehøj" .nil

#eval oregonianPeaks.zip danishPeaks


-- ### Vect.map

def Vect.map (f : α → β) : Vect α n → Vect β n
  | .nil => .nil
  | .cons x xs =>
    .cons (f x) <| map f xs

#eval oregonianPeaks.map (·.length)


-- ### Vect.zipWith

def Vect.zipWith (f : α → β → γ) : Vect α n → Vect β n → Vect γ n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys =>
    .cons (f x y) <| zipWith f xs ys

#eval oregonianPeaks.zipWith (· ++ ·) danishPeaks


-- ### Vect.unzip

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let p := unzip xys
    (.cons x p.fst, .cons y p.snd)

#eval Vect.unzip <| oregonianPeaks.zip danishPeaks


-- ### Vect.snoc

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, y =>
    .cons y .nil
  | .cons x xs, y =>
    .cons x <| snoc xs y

#eval oregonianPeaks.snoc "Mt Fuji"


-- ### Vect.reverse

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs =>
    reverse xs |>.snoc x

#eval oregonianPeaks.reverse


-- ### Vect.drop

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | m + 1, .cons _ xs =>
    drop m xs

#eval danishPeaks.drop 2


-- ### Vect.take

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | m + 1, .cons x xs =>
    .cons x <| take m xs

#eval oregonianPeaks.take 1
#eval oregonianPeaks.take 2
