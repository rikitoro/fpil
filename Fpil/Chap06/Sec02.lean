import Fpil.Util.NonEmptyList

-- # Applicative Functor

instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()

structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

-- # User Input

structure RawInput where
  name : String
  birthYear : String

-- # Subtypes

#print Subtype
-- structure Subtype {α : Type} (p : α → Prop) where
--   val : α
--   property : p val

def FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by simp⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none

-- # Validated Input

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok $ f x
    | .errors errors => .errors errors

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
      | .ok g => g <$> (x ())
      | .errors errs =>
        match x () with
          | .ok _ => .errors errs
          | .errors errs' => .errors (errs ++ errs')

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩ -- h : ¬ name = ""

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) :
  Validate ε β :=
  match val with
    | .errors errs => .errors errs
    | .ok x => next x

def checkYearIsNat (year : String) :
  Validate (Field × String) Nat :=
  match year.trim.toNat? with
    | none => reportError "birth year" "Must be digits"
    | some n => pure n

def checkBirthYear (thisYear year : Nat) :
  Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear } :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, And.intro h h'⟩
    else reportError "birth year" s!"Must be no longer than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput) :
  Validate (Field × String) (CheckedInput year) :=
  CheckedInput.mk <$>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
    checkBirthYear year birthYearAsNat

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "Mike", birthYear := "2025"}
#eval checkInput 2023 {name := "David", birthYear := "xyxasd"}
#eval checkInput 2023 {name := "", birthYear := "2000"}
#eval checkInput 2023 {name := "", birthYear := "2025"}
#eval checkInput 2023 {name := "", birthYear := "hogefuga"}
