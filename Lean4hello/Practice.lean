/-
# 練習
-/
namespace Practice

/-
## if-then-else (cond)
-/

#check @cond
-- @cond : {α : Type u_1} → Bool → α → α → α
#print cond
/-
def cond.{u} : {α : Type u} → Bool → α → α → α :=
fun {α} c x y =>
  match c with
  | true => x
  | false => y
-/

#check @Decidable.decide
-- decide : (p : Prop) → [h : Decidable p] → Bool

def f (n : Nat) : Nat :=
  bif n = 0 then 0 else 1
#print f
/-
def Practice.f : Nat → Nat :=
fun n => bif decide (n > 0) then 1 else 0
-/

-- bif-then-else は cond の別表記
example : (bif n > 0 then OfNat Nat 1 else OfNat Nat 0)
          = cond (decide (n > 0)) (OfNat Nat 1) (OfNat Nat 0) := rfl

example : cond (decide (0 = 0)) 1 0 = 1 := rfl
example : cond (decide (1 = 0)) 1 0 = 0 := rfl

#check @decide_eq_true
-- @decide_eq_true : ∀ {p : Prop} [inst : Decidable p], p → decide p = true
#check @decide_eq_true (1 = 2)
-- @decide_eq_true (1 = 2) : ∀ [inst : Decidable (1 = 2)], 1 = 2 → decide (1 = 2) = true
variable (h : 1 = 2)
#check decide_eq_true h
-- decide_eq_true h : decide (1 = 2) = true

example (n : Nat) : n > 0 → 0 < n := -- id
  fun h : n > 0 => h

example : f 0 = 0 := rfl
example (n : Nat) : n = 0 → f n = 0 :=
  fun h : n = 0 =>
    calc bif n = 0 then 0 else 1
      _ = bif true then 0 else 1 := congrArg (bif · then _ else _) (decide_eq_true h)
   -- _ = 0                      := rfl
example (n : Nat) : n > 0 → f n = 1 :=
  fun h : n > 0 =>
    calc bif n = 0 then 0 else 1
      _ = bif false then 0 else 1 := congrArg (bif · then _ else _) (decide_eq_false (Nat.not_eq_zero_of_lt h))

-- if-then-else は ite の別表記
example : (if n = 0 then OfNat Nat 0 else OfNat Nat 1)
          = ite (n = 0) (OfNat Nat 0) (OfNat Nat 1) := rfl
example : ite True (OfNat Nat 0) (OfNat Nat 1) = OfNat Nat 0 := rfl

def f' (n : Nat) : Nat :=
  if n = 0 then 0 else 1

example (n : Nat) : n = 0 → f' n = 0 :=
  fun h : n = 0 =>
    calc f' n
      _ = if n = 0 then 0 else 1 := rfl
      _ = 0                      := if_pos h

#check if_pos
-- if_pos.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α}
--            : (if c then t else e) = t
#check if_neg
-- if_neg.{u} {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α}
--            : (if c then t else e) = e
