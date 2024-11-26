import Ch4.StandardClasses
-- Monad Class Type
#print Option
-- inductive Option.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- Option.none : {α : Type u} → Option α
-- Option.some : {α : Type u} → α → Option α


-- self-define Option' in Ch1
-- inductive Option' (α : Type) : Type where
-- | none : Option' α
-- | some (value: α) : Option' α

-- #print Option'
-- inductive Option' : Type → Type
-- number of parameters: 1
-- constructors:
-- Option'.none : {α : Type} → Option' α
-- Option'.some : {α : Type} → α → Option' α


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

-- here `list[2]` actually use List.get?

#eval getThirdFourth [5, 4, 3, 2, 1] -- some (3, 4)


-- assume use Except (defined inside Lean and in the textbook) as Result in Rust
inductive Result (ε : Type) (α : Type) where
| ok (x: α) : Result ε α
| error (e : ε) : Result ε α
deriving Repr

#check List.get?

-- def get? : (as : List α) → (i : Nat) → Option α
--   | a::_,  0   => some a
--   | _::as, n+1 => get? as n
--   | _,     _   => none


def List.getResult {α : Type} (n: Nat) (l: List α) : Result String α :=
  -- Construct Result from option used `List.get?`
  match l[n]? with
  | none => Result.error s!"[Error] List.getResult error."
  | some a => Result.ok a


-- if not use List.get? ( a recursive function )
-- need to define inside List.getResult

def List.getResult' {α : Type} (n: Nat) (l: List α) : Result String α :=
  match l, n with
  | x::_, 0 => Result.ok x
  | _::xs, k + 1 => List.getResult' k xs
  | [] , _ => Result.error s!"[Error] List.getResult' error."


def getResultThirdFourth {α : Type} (l: List α) : Result String (α × α) :=
  match l[2]? with
  | none => Result.error s!"[Error] List.getResult error."
  | some a => match l[3]? with
    | none => Result.error s!"[Error] List.getResult error."
    | some b =>
    Result.ok (a, b)

-- define andThen for Result

def Result.andThen {α β ε: Type} (r: Result ε α) (f: α → Result ε β) : Result ε β :=
  match r with
  | ok x => f x
  | error e => Result.error e -- we need to construct Result ε β  from given instance e : ε  --care the type return is not ε

def rok  (x: α) : Result ε α := Result.ok x  -- with the help of automatic implicit arguments we dont need to give {α ε :Type}
def rfa  (e: ε) : Result ε α := Result.error e

-- rewrite some func

def List.getResult'' (n: Nat) (l : List α) : Result String α :=
  match l[n]? with
  | none => rfa s!"[Error] List.getResult'' error."
  | some x => rok x

-- use Result.andThen
def getResultThirdFourth' (l: List α) : Result String (α × α) :=
  Result.andThen (List.getResult'' 2 l) fun third =>
  Result.andThen (List.getResult'' 3 l) fun fourth =>
  rok (third,fourth)

-- try use accessor dot notation
def getResultThirdFourth'' (l: List α) : Result String (α × α) :=
  (List.getResult'' 2 l).andThen fun third =>
  (List.getResult'' 3 l).andThen fun fourth =>
  rok (third, fourth)

-- use infix operators
infixl:55 " ~~> " => Result.andThen
infixl:90 " <r> " => List.getResult
def getResultThirdFourth''' (l: List α) : Result String (α × α) :=
  2 <r> l ~~> fun third =>
  3 <r> l ~~> fun fourth =>
  rok (third, fourth)

-- try a proof
theorem eqGetResultThirdFourth  : getResultThirdFourth [1,2,3,4]  = getResultThirdFourth''' [1,2,3,4] := by
  unfold getResultThirdFourth getResultThirdFourth'''
  unfold Result.andThen
  unfold List.getResult
  simp
  unfold rok
  rfl
--

-- For larger
def noobGetResultEvenPositions (l: List α) : Result String (α × α × α × α) :=
  0 <r> l ~~> fun u0 =>
  2 <r> l ~~> fun u1 =>
  4 <r> l ~~> fun u2 =>
  6 <r> l ~~> fun u3 =>
  rok (u0,u1,u2,u3)


-- and then in Logging
def isEven : Int → Bool :=
  fun x =>  x % 2 == 0

def sumAndFindEven : List Int → List Int × Int
  | [] => ([], 0)
  | x :: xs =>
    let (l, acc) := sumAndFindEven xs
    if isEven x then (x::l, acc+x) else (l, acc+x)

-- try tail recursion
def sumAndFindEven' : List Int → List Int × Int :=
  let rec aux (l: List Int) (ll: List Int) (acc: Int) : List Int × Int :=
    match l with
    | [] => (ll, acc)
    | x::xs => if isEven x then aux xs (x::ll) (acc+x) else aux xs ll (acc+x)
  fun l => aux l.reverse [] 0

-- give an example of equ
def test_eq_even_list : List Int := [8,1,4,11]
theorem eqSumAndFindEven : sumAndFindEven test_eq_even_list = sumAndFindEven' test_eq_even_list := by
  unfold test_eq_even_list
  unfold sumAndFindEven'
  repeat unfold sumAndFindEven sumAndFindEven'.aux isEven
  simp_all
  -- unfold sumAndFindEven sumAndFindEven'.aux isEven
  -- simp
  -- unfold sumAndFindEven sumAndFindEven'.aux isEven
  -- simp
  -- unfold sumAndFindEven sumAndFindEven'.aux isEven
  -- simp
  -- unfold sumAndFindEven sumAndFindEven'.aux
  -- simp --be careful cbout l.reverse


structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val: α
deriving Repr

-- reminder
-- inductive Option α
-- | some a
-- | none
-- def Option.andThen (o: Option α) (next: α → Option β) : Option β


-- inductive Result ε α
-- | error e
-- | ok a
-- def Result.andThen (r: Result ε α) (next: α → Result ε β) : Result ε β

-- addThen written for inductive datatypes (actually sum datatypes without recursion)
-- may consider Option α as Option α Un and constructor none Un. Un meas accept no parameters

-- now back to addThen on WithLog (p： Product Type)
-- personnally with one type stay constant (as the log type)and the other type change (for example to construct α × α × α according to the reputation of the function)
-- Another example is just pack from the lowest type (e.g. RawBytes) to upper protocol items (e.g. Message andthen IpPack andthen HttpPack)

def WithLog.andThen (l: WithLog α β) (f: β → WithLog α γ) : WithLog α γ :=
  -- not the same as solve Sum Type in branches
  -- construct all components of Product Type
  let {log := log1, val := val1} := l
  let {log := log2, val := val2} := f val1
  {log := log1 ++ log2, val := val2}


def sumAndFindEven'' : List Int → WithLog String Int
  | [] => {log := [], val := 0}
  | x :: xs =>
    -- with given function
    WithLog.andThen (if isEven x then {log:= [s!"{x} is even\n"], val := ()} else {log:= [], val := ()}) fun () => -- to Type Withlog String Int
    WithLog.andThen (sumAndFindEven'' xs) fun acc =>
    {log:= [], val := acc + x}

    -- With the help of WithLog String Unit
    -- we can decouple logging event out from calculation
    -- Still a little bit confuse
    -- From the textbook
    -- ```WithLog, andThen, ok, and save can be used to separate the logging concern from the summing concern in both programs:```




def ok (x : β) : WithLog α β := {log := [], val := x}


def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => WithLog.andThen
-- rewrite use ok


def save_with_check (x: Int) : WithLog String Unit :=
  if isEven x then {log := [s!"{x} is even\n"], val := ()} else {log := [], val := ()}

def sumAndFindEven''' : List Int → WithLog String Int
  | [] => {log := [], val := 0}
  | x :: xs =>
    -- with given function
    save_with_check x ~~> fun () =>
    sumAndFindEven''' xs ~~> fun acc =>
    ok (acc + x)

def sumAndFindEvenExtraLog : List Int → WithLog String Int
  | [] => {log := [], val := 0}
  | x :: xs =>
    -- with given function
    save_with_check x ~~> fun () =>
    --- add extra log in place1
    save s!"[ExtraLog] in place1\n" ~~> fun () =>
    sumAndFindEvenExtraLog xs ~~> fun acc =>
    save s!"[ExtraLog] in place2\n" ~~> fun () =>
    ok (acc + x)

instance : ToString (WithLog String Int) where
  toString w :=
  let logStr := String.join w.log
  s!"WithLog:\nlog:\n" ++ logStr ++ "\n\nval: " ++ toString w.val

def test_even_list : List Int := [8,1,-1,11,5,4]

#eval sumAndFindEven test_even_list
#eval sumAndFindEven'' test_even_list
#eval sumAndFindEvenExtraLog test_even_list


def save_node_value (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

#check BinTree
-- def exampleTree : BinTree Nat :=
--   BinTree.node (BinTree.node BinTree.leaf 1 BinTree.leaf) 2 (BinTree.node BinTree.leaf 3 BinTree.leaf)

def inorderSum : BinTree Nat → WithLog Nat Nat
  | BinTree.leaf => ok 0
  | BinTree.node l x r =>
    inorderSum l ~~> fun leftSum =>
    save_node_value x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)

#print exampleTree
#eval inorderSum exampleTree

def preorderSum : BinTree Nat → WithLog Nat Nat
  | BinTree.leaf => ok 0
  | BinTree.node l x r =>
    save_node_value x ~~> fun () =>
    inorderSum l ~~> fun leftSum =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)

def postorderSum : BinTree Nat → WithLog Nat Nat
  | BinTree.leaf => ok 0
  | BinTree.node l x r =>
    inorderSum l ~~> fun leftSum =>
    inorderSum r ~~> fun rightSum =>
    save_node_value x ~~> fun () =>
    ok (leftSum + x + rightSum)

#eval preorderSum exampleTree
#eval postorderSum exampleTree


-- Monads: A Functional Design Pattern
-- Each of these examples has consisted of:

-- A polymorphic type, such as Option, Except ε, WithLog logged, or State σ
-- An operator andThen that takes care of some repetitive aspect of sequencing programs that have this type ↑
-- An operator ok that is (in some sense) the most boring way to use the type
-- A collection of other operations, such as none, fail, save, and get, that name ways of using the type


-- the trivial ok op to use this type and the andThen op dont need to re reimplementation

-- check Monad class defination

#check Monad
-- class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
--   map      f x := bind x (Function.comp pure f)
--   seq      f x := bind f fun y => Functor.map y (x ())
--   seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
--   seqRight x y := bind x fun _ => y ()

instance : Monad Option where
  pure x := some x
  bind opt f := match opt with
    | none => none
    | some x => f x



instance : Monad (Result ε) where
  pure x := Result.ok x
  bind res f := match res with
    | Result.error e => Result.error e
    | Result.ok x => f x


def getFirstThirdFourth : List α → Option (α × α × α) :=
  fun l =>
  l[0]? >>= fun first =>
  l[2]? >>= fun third =>
  l[3]? >>= fun fourth =>
  pure (first, third, fourth)

-- give an example
#eval getFirstThirdFourth [1,2,3,4,5] -- some (1, 3, 4)


-- lookup represent the way to pick up the element to Monad
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]


-- instance search for Monad Option because xs[i] for xs : List return Option
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

-- try result
#eval firstThirdFifthSeventh (fun xs i => List.getResult i xs) fastBirds

def kindOfGeneral [Monad m] (f : α → m β) (xs : List α) : m (List β) :=
  match xs with
    | [] => pure []
    | x :: xs' =>
      f x >>= fun x' =>
      kindOfGeneral f xs' >>= fun xs'' =>
      pure (x' :: xs'')

-- is actually mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
-- observion : compare to firstThirdFifthSeventh
-- more general f?
-- but design to return (List β) instead of independent type γ (also requires input as List sequence)

-- general on all Monad (input and output as List)
-- a little different from firstThirdFifthSeventh because use f: List α → m β  (actually the List α is the parameter of entrance)  instead of f: α → m β

-- represent the state change of value
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def ok_state(x: α) : State σ α := fun s => (s, x)
def set_state(s: σ) : State σ Unit := fun _ => (s, ())
def get_state : State σ σ := fun s => (s, s)
--- well..... consider take func as polymorphic type in the Monad

-- instance : Monad (State σ) where
--   pure x := fun s => (s, x)  -- function type define (comparing Sum Type and Product Type)
--   bind state f := fun s =>  -- function type
--     let (s', a) := state s
--     f a s'


instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int := -- and save prefix sum (not included) in new state
  get_state >>= fun i =>
  set_state (i + howMuch) >>= fun () =>
  pure i

-- α → m β  here is Int → State Int Int
#check mapM increment [1, 2, 3, 4, 5]  -- become a monad ouput State Int (List Int)

-- because State is actually a function type σ → (σ × α)  (σ × α) is the product type
-- if we wanna the final ouput we need to give the initial int state
#eval (mapM increment [1, 2, 3, 4, 5]) 0 -- (15, [1, 3, 6, 10, 15])

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i

#eval mapM saveIfEven [1, 2, 3, 4, 5]


-- Exercise Ch5.1
-- Review the previous definition of mapM (on List seque)
-- Define a function BinTree.mapM. By analogy to mapM for lists, this function should apply a monadic function to each data entry in a tree, as a preorder traversal. The type signature should be:


-- Monad m should be found first for the value (which is type α used for BinTree α)
-- consider the type signature of mapM
-- def mapM [Monad m] (f : α → m β) : List α → m (List β)
#check BinTree
def BinTree.mapM [Monad m] (f : α → m β): BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.node l v r =>
    BinTree.mapM f l >>= fun l' =>
    f v >>= fun v' =>
    BinTree.mapM f r >>= fun r' =>
    pure (BinTree.node l' v' r')
-- done

-- def the Nat form
def incrementNat (howMuch : Nat) : State Nat Nat := -- and save prefix sum (not included) in new state
  get_state >>= fun i =>
  set_state (i + howMuch) >>= fun () =>
  pure i


-- redifine the output style
def treeOutPutStyle (b: BinTree Nat) : String :=
  match b with
  | BinTree.leaf => ""
  | BinTree.node l v r => "{" ++ (treeOutPutStyle l) ++ s!" {v} " ++ (treeOutPutStyle r) ++ "}"

instance : ToString (BinTree Nat) where
  toString bt := treeOutPutStyle bt

-- give some examples
#eval s!"{exampleTreeLarge}"
#eval s!"{BinTree.mapM incrementNat exampleTreeLarge 0}"
-- from this we lean that mapM

-- From this example, we understand that the mapM defined on BinTree specifies a sequential access order.
-- e.g. if mapM defined as just like the definition above
-- the increment tree will follow inorder
-- "(16, {{{ 0 } 1 { 3 }} 6 {{ 10 } 11 { 13 }}})"
-- not formal ∀ nl ∈ leftree , rl ∈ righttree, nl < v < rl


def BinTree.mapMl [Monad m] (f : α → m β): BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.node l v r =>
    f v >>= fun v' =>
    BinTree.mapMl f l >>= fun l' => -- careful for the function name for recursive cal
    BinTree.mapMl f r >>= fun r' =>
    pure (BinTree.node l' v' r')

def BinTree.mapMr [Monad m] (f : α → m β): BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.node l v r =>
    BinTree.mapMr f l >>= fun l' =>
    BinTree.mapMr f r >>= fun r' =>
    f v >>= fun v' =>
    pure (BinTree.node l' v' r')

-- lets check the difference of 3 definition mapM
/-
"(16, {{{ 0 } 1 { 3 }} 6 {{ 10 } 11 { 13 }}})"

-/
#eval s!"{BinTree.mapM incrementNat exampleTreeLarge 0}"
/-
"(16, {{{ 6 } 4 { 7 }} 0 {{ 12 } 10 { 13 }}})"

-/
#eval s!"{BinTree.mapMl incrementNat exampleTreeLarge 0}"
/-
"(16, {{{ 0 } 4 { 1 }} 12 {{ 6 } 10 { 7 }}})"

-/
#eval s!"{BinTree.mapMr incrementNat exampleTreeLarge 0}"


-- The Option Monad Contract

-- Convincing argument thaat the Monad Instance for `Option`

-- Proof of `Id` monad at first
def Id'' (t : Type) : Type := t

instance : Monad Id'' where
  pure x := x
  bind x f := f x


-- instance : Monad Option where
--   pure x := some x
--   bind opt next := none

theorem left_identity_pure_for_id (x : α) (f: α → Id'' β) : bind (pure x) f = f x := by simp
theorem right_identity_pure_for_id (x: Id'' α) : bind x pure = x := by simp
theorem associative_bind_for_id (x : α) (f: α → Id'' β) (g: β → Id'' γ) : bind (bind x f) g = bind x (fun y => bind (f y) g) := by simp

-- Try proof
instance : Monad Option where
  pure x := some x
  bind opt f := match opt with
    | none => none
    | some x => f x

theorem left_identity_pure_for_option (x : α) (f: α → Option β) : bind (pure x) f = f x := by
  rw [Option.pure_def]
  unfold bind
  -- sorry

-- But we get to know why
-- instance : Monad Option where
--   pure x := some x
--   bind opt next := none
-- because in this step  bind opt will always construct from none
-- with the goal like none = f x (given the fact ∃ f, exact pure, leading to conflicting goals)


theorem right_identity_pure_for_option (x: Option α) : bind x pure = x := by
  sorry

theorem associative_bind_for_for_option (x : α) (f: α → Option β) (g: β → Option γ) : bind (bind x f) g = bind x (fun y => bind (f y) g) := by
  sorry

-- The identity monad
def Id' (t : Type) : Type := t -- guess construct t=t?

instance : Monad Id' where
  pure x := x
  bind x f := f x
  -- bind : {α β : Type} → Id' α → (α → Id' β) → Id' β
  -- reduce to (may beta-reduction in Category Theory)  α → (α → Id' β) → β

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]
-- explicitly given to find Monad instance as Id instance

def test_id_f1 := fun x => x + 1 -- can be recognized as α → Monad β with Id instance

def test_id_f2 := fun (_: Int) => "test"

-- #eval mapM (· + 1) [1, 2, 3, 4, 5]
  -- failed to synthesize
  -- HAdd Nat Nat (?m.32590 ?m.32592)

-- #eval mapM test_id_f1 [1, 2, 3, 4, 5]
-- typeclass instance problem is stuck, it is often due to metavariables
--   Monad ?m.32590

-- #eval mapM test_id_f2 [1, 2, 3, 4, 5]
-- typeclass instance problem is stuck, it is often due to metavariables
--   Monad ?m.32590
#eval mapM (m := Id') test_id_f2 [1, 2, 3, 4, 5]
-- ["test", "test", "test", "test", "test"]
-- ✌️ now we use mapM as map


-- The Monad Contract
-- 1. First, `pure` should be a left identity of bind, `bind (pure v) f` should be the same as f v`
-- 2. Secondly, `pure` should be a right identity of bind, so `bind v pure` is the same as v. Finally, `bind` should be associative, so `bind (bind v f) g` is the same as `bind v (fun x => bind (f x) g)`.

-- `bind (bind v f) g` is the same as `bind v (fun x => bind (f x) g)`.  need deeper understanding
-- try infix expression?


-- Create a combination of bind op chains
-- expalin in Option Monad

-- Bind As Lazy Chaining
-- 	1.	bind as Lazy Chaining:
-- bind can be interpreted as a lazy chaining operator that connects computations within a monadic context. This deferred approach ensures computations are performed only when absolutely necessary.
-- 	2.	Benefits of Lazy Chaining:
-- 	•	It prevents wasteful evaluations, particularly in contexts like Option (to short-circuit unnecessary calculations) or asynchronous computations (to defer costly operations).
-- 	•	It enables flexible recomposition of binding chains, which is crucial for complex dependency management.
-- 	•	It guarantees associativity by allowing operations to be rearranged or grouped without impacting the final result. This ensures consistency in the behavior of the Monadic operations, even in non-trivial pipelines such as nested bind calls.

-- This abstraction makes bind particularly well-suited for modeling workflows that involve asynchronous processing, error handling, or managing dependencies dynamically.
