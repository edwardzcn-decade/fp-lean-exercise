-- simp tatic changed the default of simp
-- https://proofassistants.stackexchange.com/questions/3941/help-needed-for-lean4-book-interlude-exercise
--
-- chore: change simp default to decide := false #1888
-- https://github.com/leanprover/lean4/pull/1888
-- theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp
-- In Lean v4.3.0, "simp will no longer try to use Decidable instances to rewrite terms" by default (release notes). This change broke these proofs in chapter 3:
theorem addAndAppend: 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  simp [String.append]
-- now work

theorem addAndAppend': 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

theorem addAndAppend'': 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  simp (config:= {decide := true})

-- proof
theorem andImpliesOr : A ∧ B → A ∨ B := by
  intro H
  cases H with
  | intro hA hB =>
    apply Or.inl; exact hA


-- caculate
theorem andImpliesOr' : A ∧ B → A ∨ B :=
  fun a_and_b =>
    match a_and_b with
    | And.intro a _ => Or.inl a


theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 7 < 5 := by
  apply Or.inl
  rfl

-- or just simp

theorem onePlusOneAndLessThan' : 1 + 1 = 2 ∨ 7 < 5 := by
  simp


theorem onePlusOneAndLessThan'' : 1 + 1 = 2 ∨ 3 < 5 :=
  Or.inl rfl

theorem onePlusOneAndLessThan''' : 1 + 1 = 1 + 1 ∨ 3 < 5 :=
  Or.inl (Eq.refl (1+1))
-- without other mk functions Eq.refl only create a = a (exactly the same) but rfl can make (1 + 1 = 2)

theorem notTwoEqualFive : ¬(1 + 1 = 5) := by
  simp

theorem notTwoEqualFive' : ¬(1 + 1 = 5) := by
  intro H
  contradiction

-- theorem notTwoEqualFive'' : ¬(1 + 1 = 5) := -- equal to 1 + 1 = 5 -> False

#print notTwoEqualFive
#print notTwoEqualFive'
#print of_eq_false
#print of_decide_eq_false


#check Eq.refl (decide (1 + 1 = 5))


theorem notTwoEqualFive'' : ¬(1 + 1 = 5):=
  fun H => -- From type H: 1 + 1 = 5 construct False
    -- #check (absurd H (of_decide_eq_false (Eq.refl (decide (1 + 1 = 5)))))
    absurd H (of_decide_eq_false (Eq.refl (decide (1 + 1 = 5))))

theorem trueIsTrue : True := by simp
theorem trueIsTrue' : True := True.intro

theorem trueOrFalse : True ∨ Faluse := by simp
theorem trueOrFalse' : True ∨ False := Or.inl True.intro


-- cant prove False
-- False is a propsition that has no proofs in Lean
-- If you get a False as hypothesis. You can prove anything using False.elim
-- theorem falseIsFalse : False :=

theorem falseImpliesTrue : False → True := by simp
theorem falseImpliesTrue' : False → True := by
  intro H
  apply False.elim H
theorem falseImpliesTrue'' : False → True :=
  fun H => False.elim H

theorem falseImpliesAnything (P : Prop) (h: False) : P := by
  apply False.elim h


-- def third (xs : List α) : α := xs[2] -- not safe due to the length of the list may less than 3
def third (xs : List α) : Option α := xs.get? 2

def test_list := [1,1,2]
#eval third test_list

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

-- add evidence
def third' (xs : List α) (evidence : xs.length > 2) : α := xs[2]
#eval third' woodlandCritters (by decide)
#eval third' test_list (by decide)

def third'' (xs: List α) : Option α := xs[2]?
#eval third'' test_list

-- exercise

theorem twoPlusThreeEqFive : 2 + 3 = 5 := by rfl
theorem fifteenMinusEightEqSeven : 15 - 8 = 7 := by rfl
theorem stringAppendEq : "Hello, ".append "world" = "Hello, world" := by rfl
-- theorem fiveLeEighteen : 5 < 18 := by rfl --not a reflexive relation
theorem fiveLeEighteen : 5 < 18 := by
  simp


theorem twoPlusThreeEqFive' : 2 + 3 = 5 := by simp
theorem fifteenMinusEightEqSeven' : 15 - 8 = 7 := by simp
theorem stringAppendEq' : "Hello, ".append "world" = "Hello, world" := by
  decide
-- theorem fiveLeEighteen : 5 < 18 := by rfl --not a reflexive relation
theorem fiveLeEighteen' : 5 < 18 := by
  decide
