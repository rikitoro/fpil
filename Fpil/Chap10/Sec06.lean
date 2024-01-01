/- # Insertion Sort and Array Mutation -/

#check dbgTraceIfShared

-- # The Inner Loop

def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*]⟩

#check Nat.lt_of_succ_lt

-- # The Outer Loop

-- partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
--   if h : i < arr.size then
--     insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
--   else
--     arr

-- #eval insertionSortLoop #[3, 1, 4, 1, 5, 9, 2, 6] 0

-- #eval insertionSortLoop #["metamorphic", "igneous", "sedentary"] 0

-- ## Termination

-- theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
--   (insertSorted arr i).size == arr.size := by
--   match i with
--   | ⟨j, isLt⟩ =>
--     induction j with
--     | zero => simp [insertSorted]
--     | succ j' ih =>
--       simp [insertSorted]
--       split <;> try rfl

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
  (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
  (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, hLen]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    split <;> try simp[*]


def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : Array.size (insertSorted arr ⟨i, h⟩) - (i + 1) < Array.size arr - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      simp [Nat.sub_succ_lt_self, *]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
  termination_by insertionSortLoop arr i => arr.size - i

-- # The Driver Function

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

#eval insertionSort #[3, 1, 7, 4]
#eval insertionSort #[ "quartz", "marble", "granite", "hematite"]

def insertSorted' [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted'
        ((dbgTraceIfShared "array to swap" arr).swap ⟨i', by assumption⟩ i)
        ⟨i', by simp [dbgTraceIfShared, *]⟩

theorem insert_sorted_size_eq' [Ord α] (len : Nat) (i : Nat) :
  (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
  (insertSorted' arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted', *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted', dbgTraceIfShared]
    split <;> simp [*]

def insertionSortLoop' [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted' arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq' arr.size i arr h rfl]
      simp [Nat.sub_succ_lt_self, *]
    insertionSortLoop' (insertSorted' arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by insertionSortLoop' arr i => arr.size - i

def insertionSort' [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop' arr 0

#eval insertionSort' #[3, 1, 7, 4]
#eval insertionSort' #[ "quartz", "marble", "granite", "hematite"]


def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  pure lines

def mainUnique : IO Unit := do
  let lines ← getLines
  for line in insertionSort' lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in insertionSort' lines do
    IO.println line
  --
  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do
    IO.println line
