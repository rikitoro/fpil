structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
