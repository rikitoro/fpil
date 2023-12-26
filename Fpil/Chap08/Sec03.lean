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
