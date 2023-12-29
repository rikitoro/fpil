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
