-- # The Universe Design Pattern

inductive NatOrBool where
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool

def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none

#eval decode NatOrBool.nat "42"
#eval decode NatOrBool.nat "seven"
#eval decode NatOrBool.bool "true"
#eval decode NatOrBool.bool "false"
#eval decode NatOrBool.bool "hoge"

inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2

def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y

-- instance {t : NestedPairs} : BEq t.asType where
--   beq x y := x == y
--
-- failed to synthesize instance
--   BEq (NestedPairs.asType t)

-- # A Universe of Finite Types

inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite -- arrow

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
  match t with
  | .unit =>
    results.map fun r =>
      fun () => r
  | .bool -- !!!implement here!!!

def Finite.enuerate (t : Finite) : List t.asType :=
  | .unit => [()]
  | .bool => [true, false]
  | .pair t1 t2 => t1.enumerate.product t2.enumerate
  | .arr t1 t2 => t1.functions t2.enumerate

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2 =>
    t1.enumerate.all fun arg => beq t2 (x arg) (y arg) -- すべての引数 arg に対して x arg == y arg

#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
