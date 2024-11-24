-- Monad Class Type

-- And then (like in the Rust)
def andThen (option : Option α) (next : α → Option β) :=
  match option with
  | none => none
  | some value => next value

def getThirdFourth : List α → Option (α × α) :=
  fun list =>
  andThen list[2]? fun third =>
  andThen list[3]? fun fourth =>
  some (third, fourth)

#eval getThirdFourth [5, 4, 3, 2, 1] -- some (3, 4)
