import Fpil.Chap07.Sec02

-- # Ordering Monad Transformers

def countLetters' [Monad m] [MonadState LetterCounts m] [MonadExcept Err' m] (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

abbrev M1 := StateT LetterCounts (ExceptT Err' Id)
abbrev M2 := ExceptT Err' (StateT LetterCounts Id)

#eval countLetters' (m := M1) "hello" ⟨0, 0⟩
#eval countLetters' (m := M2) "hello" ⟨0, 0⟩

#eval countLetters' (m := M1) "hello!ab" ⟨0, 0⟩
#eval countLetters' (m := M2) "hello!ab" ⟨0, 0⟩

def countWithFallback
  [Monad m] [MonadState LetterCounts m] [MonadExcept Err' m]
  (str : String) : m Unit :=
  try
    countLetters' str
  catch _ =>
    countLetters' "Fallback"

#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩
#eval countWithFallback (m := M1) "hello!a" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello!a" ⟨0, 0⟩
