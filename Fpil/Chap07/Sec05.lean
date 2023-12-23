-- # Additional Conveniences

-- # Pipe Operators

#eval some 5 |> toString
#eval toString <| some 5
#eval toString $ some 5

def times3 (n : Nat) : Nat := n * 3

#eval 5 |> times3 |> toString |> ("It is " ++ · )
#eval ("It is " ++ · ) <| toString <| times3 <| 5
#eval ("It is " ++ · ) $ toString $ times3 5

#eval [1, 2, 3].reverse
#eval List.reverse [1, 2, 3]

#eval ([1, 2, 3].reverse.drop 1).reverse
#eval [1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse

-- # Infinite Loops

def spam : IO Unit := do
  repeat IO.println "Spam!"

-- #eval spam

def bufsize : USize := 20 * 1024

def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf

-- # While Loops

def dump'(stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize
