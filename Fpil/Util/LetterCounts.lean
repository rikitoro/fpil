
structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdefghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)
