-- # Worked Example: Typed Queeies

-- # A Universe of Data

inductive DBType where
  | int | string | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool

#eval ("Mount Hood" : DBType.string.asType)
#eval ("Mount Hood" : DBType.asType DBType.string)

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance : BEq DBType where
  beq
  | .int, .int => true
  | .string, .string => true
  | .bool, .bool => true
  | _, _ => false

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec

-- # Schemas and Tables

structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2 :: cols)

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema := [
  ⟨"name", DBType.string⟩,
  ⟨"location", DBType.string⟩,
  ⟨"elevation", DBType.int⟩,
  ⟨"lastVisited", .int⟩
]

def mountainDiary : Table peak := [
  ("Mount Nebo",        "USA",      3637, 2013),
  ("Moscow Mountain",   "USA",      1519, 2015),
  ("Himmelbjerget",     "Denmark",   147, 2004),
  ("Mount St. Helens",  "USA",      2549, 2010)
]

abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]

def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]

-- # Recursion and Universes, Revisited

-- def Row.bEq (r1 r2 : Row s) : Bool :=
--   match s with
--   | [] => true
--   | col :: cols =>
--     match r1, r2 with
--     | (v1, r1'), (v2, r2') =>
--       v1 == v2 && bEq r1' r2'
-- --
-- type mismatch
--   (v1, r1')
-- has type
--   ?m.11890 × ?m.11893 : Type (max ?u.11902 ?u.11901)
-- but is expected to have type
--   Row (col :: cols) : Type

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _ :: _ :: _ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

-- # Column Pointers

inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

-- # Subschemas

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
    HasCol bigger n t →
    Subschema smaller bigger →
    Subschema (⟨n, t⟩ :: smaller) bigger

abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

example : Subschema travelDiary peak :=
  .cons .here $
    .cons (.there .here) $
      .cons (.there <| .there <| .there .here) .nil

example : Subschema [] peak := by
  constructor

example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
  constructor

example : Subschema [⟨"location", .string⟩] peak :=
  .cons (.there .here) .nil

example : Subschema [⟨"location", .string⟩] peak := by
  repeat constructor

example : Subschema travelDiary peak := by
  repeat constructor

example : Subschema travelDiary waterfall := by
  repeat constructor

def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
  match sub with
  | .nil => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

-- # Projecting Rows

def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
