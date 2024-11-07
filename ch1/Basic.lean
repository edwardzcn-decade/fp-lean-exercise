#eval 1 + 2
def add1 (n: Nat) := n + 1
#eval add1 1
#eval (1 + 2) * 5
#eval String.append "Hello," "Lean"
#eval String.append "Hello," "world"

#eval String.append "it is " (if 1>2 then "yes" else "no")
#check (1 - 2: Int)
def test_if_int := 1-2
#check (test_if_int: Int)
#check (test_if_int: Nat)
-- #check String.append "Hello" ["", "world"]


#eval String.append "it is " (if 1 > 2 then "yes" else "no")

def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)


-- def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
-- ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε


-- 1.3

def add2 (n: Nat): Nat := n + 1

#eval (add1 2) = (add2 2)
#eval add1 2

def maximum (n: Nat) (m: Nat): Nat :=
if n > m then n else m
#check (maximum: Nat -> Nat -> Nat)

-- self exercise

def maximum7 (n: Nat): Nat := (maximum 7 n)
#check (maximum7: Nat -> Nat)

def maximum7' (n: Nat): Nat := (maximum n 7)
#check (maximum7': Nat -> Nat)



-- Exercise
-- Define the function joinStringsWith with type String -> String -> String -> String that creates a new string by placing its first argument between its second and third arguments. joinStringsWith ", " "one" "and another" should evaluate to "one, and another".
def joinStringsWith (split: String) (left: String) (right: String) : String :=
  String.append left (String.append split right)
#eval joinStringsWith " " "Hi" "edward"



-- What is the type of joinStringsWith ": "? Check your answer with Lean.
-- The type of `joinStringsWith ": "` should be `String → String → String`
#check joinStringsWith ": "

-- Define a function volume with type Nat → Nat → Nat → Nat that computes the volume of a rectangular prism with the given height, width, and depth.
def volume' (height: Nat) (width: Nat) (depth: Nat) : Nat :=
  height*width*depth
#eval volume' 3 4 5

-- Defining Types
def Str: Type := String
def aStr: Str := "This is a String"
#check aStr

def thirtyEight : Nat := 38
def NaturalNumber : Type := Nat
def thirtyEight' : NaturalNumber := (38: Nat)

abbrev N: Type := Nat
def thirtyEight'' : N := 38
-- inline 展开 相当于 def thirtyEight'' : Nat := 38


-- `abbrev` instead of `def` allows overloading resolution

abbrev NaturalNumber' : Type := Nat
def thirtyEight''' : NaturalNumber' := 38

-- #eval thirtyEight' = thirtyEight''

#check (0: Float)
#check (0: Int)


-- Structures

structure Point where
  x : Float
  y : Float
deriving Repr

def p1: Point := {x := (1: Float), y := 2}
#eval p1


def addPoints (p1 : Point) (p2 : Point) : Point := {
  x := p1.x + p2.x,
  y := p1.y + p2.y
}

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (
    (p2.x - p1.x) ^ 2.0 + (p2.y - p1.y) ^ 2.0
  )

def p2: Point := {x := 0, y := 4}

#eval distance p1 p2
#eval (distance p1 p2) - Float.sqrt 5

-- Updating Structures

def zeroX (p : Point) : Point :=
  { x:= 0 , y := p.y}
def zeroX' (p : Point) : Point :=
  { p with x := 0}

def oneX (p : Point) : Point :=
  { x:= 1, y := p.y}
def oneX' (p :Point) : Point :=
  { p with x := 1}


-- make an prompt that forall X  distance between zeroX and oneX
-- is equal to 1.0
#eval p1
#eval distance (zeroX p1) (zeroX' p1)


-- Behind the Scenes (the constructor)
#check Point.mk 1.5 2.8
#check Point.mk
#check (Point.mk : Float-> Float-> Point)
#check Point.mk 1.5 2

structure Point' where
  point::
  x : Float
  y : Float
deriving Repr


def p1' : Point' := Point'.point 1 2
#eval p1'

def fourAndThree : Point' := Point'.point 4.5 3.5
#eval fourAndThree
def Point'.modifyBoth (f: Float -> Float) (p: Point') : Point' :=
{
  p with
  x := f p.x
  y := f p.y
}

#eval fourAndThree.modifyBoth (fun x => x + 1)
#eval fourAndThree.modifyBoth (Float.floor)

-- 调用Point'.modifyBoth 函数  fourAndThree 作为第一个类型T（这里是Point')参数，虽然在所有参数列表里不是第一个（而是第二个）

-- Exercise
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def volume (rect : RectangularPrism) : Float :=
  rect.height * rect.width * rect.depth

structure Segment where
  p1 : Point
  p2 : Point
deriving Repr

#check volume

def Segmant.length (s : Segment) : Float :=
  distance s.p1 s.p2
#print distance


def seg1 : Segment := {
  p1 := Point.mk 1 1,
  p2 := Point.mk 2 2
}
#eval Segmant.length seg1


--- Datatypes and Patterns
