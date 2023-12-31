/- # More Inequalities -/

-- # Merge Sort
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x' :: xs', y' :: ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x' :: xs') ys'
-- termination_by merge xs ys => xs.length + ys.length
termination_by merge xs ys => (xs, ys)

def splitList (lst : List α) : List α × List α :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

theorem Nat.succ_le_succ' : n ≤ m → Nat.succ n ≤ Nat.succ m := by
  intro h
  induction h with
  | refl => constructor
  | step _ ih =>
    constructor
    assumption

theorem Nat.succ_le_succ'' : n ≤ m → Nat.succ n ≤ Nat.succ m
  | .refl => .refl
  | .step h' => .step $ Nat.succ_le_succ'' h'

theorem Nat.le_succ_of_le' : n ≤ m → n ≤ Nat.succ m := by
  intro h
  induction h with
  | refl => constructor ; constructor
  | step => constructor ; assumption

theorem Nat.le_succ_of_le'' : n ≤ m → n ≤ Nat.succ m := by
  intro h
  induction h with
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih

theorem Nat.le_succ_of_le''' : n ≤ m → n ≤ Nat.succ m := by
  intro h
  induction h <;> repeat (first | constructor | assumption)

theorem Nat.le_succ_of_le'''' : n ≤ m → n ≤ Nat.succ m
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le'''' h)

theorem splitList_shorter_le (lst : List α) :
  (splitList lst).fst.length ≤ lst.length ∧
  (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil =>
    simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left =>
      apply Nat.succ_le_succ
      assumption
    case right =>
      apply Nat.le_succ_of_le
      assumption

theorem splitList_shorter (lst : List α) ( _ : lst.length ≥ 2) :
  (splitList lst).fst.length < lst.length ∧
  (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    -- simp [splitList]
    simp_arith [splitList]
    apply splitList_shorter_le


theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
  (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
  (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right


def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by
      apply Nat.ge_of_not_lt h
    have : List.length (splitList xs).fst < List.length xs := by
      apply splitList_shorter_fst
      assumption
    have : List.length (splitList xs).snd < List.length xs := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by mergeSort xs => xs.length

#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
#eval mergeSort [5, 3, 22, 15]

-- # Division as Iterated Sbtraction

def div (n k : Nat) (ok : k > 0) : Nat :=
  if h : n < k then
    0
  else
    have : 0 < n := by
      cases n with
      | zero => contradiction
      | succ n' => simp_arith
    have : n - k < n := by
      apply Nat.sub_lt
      assumption
      assumption
    1 + div (n - k) k ok
termination_by div n k ok => n

#eval div 10 3 (by simp)
#eval div 10 1 (by simp)
