namespace Chapter7

namespace Hidden

inductive Bool where
  | true
  | false
  deriving Repr

/-
-- Bool型の導入則
#check Bool.true
#check Bool.false

-- Bool型の除去則
#check @Bool.rec
-/

namespace Bool
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
def or (a b : Bool) : Bool :=
  match a with
  | true  => true
  | false => b
def not (a : Bool) : Bool :=
  match a with
  | true  => false
  | false => true

infixl:65 " & " => and
infixl:60 " ∣ " => or  -- `\|`
prefix:100 "¡"  => not -- `\!`

/-
-- ここで定義したand,or,notは関数
-- 3章で出てきたAnd,Or,Notは型

#print and
-- def Chapter7.Bool.and : Bool → Bool → Bool :=
-- fun a b =>
--   match a with
--   | true => b
--   | false => false

#print or
-- def Chapter7.Bool.or : Bool → Bool → Bool :=
-- fun a b =>
--   match a with
--   | true => true
--   | false => b

#print And
-- inductive And : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- And.intro : ∀ {a b : Prop}, a → b → a ∧ b

#print Or
-- inductive Or : Prop → Prop → Prop
-- number of parameters: 2
-- constructors:
-- Or.inl : ∀ {a b : Prop}, a → a ∨ b
-- Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/

theorem and_self {a : Bool} : a & a = a := -- by
  match a with
  | true  => rfl
  | false => rfl

theorem false_and {b : Bool} : false & b = false := by
  rfl
theorem and_false {a : Bool} : a & false = false := by
  cases a <;> rfl

theorem and_comm {a b : Bool} : a & b = b & a := by
  cases a <;> cases b <;> rfl

theorem and_assoc {a b c : Bool} : (a & b) & c = a & (b & c) := by
  match a with   -- `and`は左の項が決まれば簡約できて...
  | true  => rfl -- and b c = and b c
  | false => rfl -- false = false

theorem or_self {a : Bool} : (a ∣ a) = a := by
  cases a <;> rfl

theorem true_or {b : Bool} : (true ∣ b) = true := by
  rfl
theorem or_true {a : Bool} : (a ∣ true) = true := by
  cases a <;> rfl

theorem or_comm {a b : Bool} : (a ∣ b) = b ∣ a := by
  cases a <;> cases b <;> rfl

theorem or_assoc {a b c : Bool} : (a ∣ (b ∣ c)) = a ∣ (b ∣ c) := by
  cases a <;> rfl

theorem or_and {a b c : Bool} : (a ∣ b) & c = a & c ∣ b & c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem not_true  : ¡ true = false := rfl
theorem not_false : ¡ false = true := rfl

theorem de_morgan_1 {a b : Bool} : ¡ (a & b) = ¡a ∣ ¡b := by
  cases a <;> rfl
theorem de_morgan_2 {a b : Bool} : ¡ (a ∣ b) = ¡a & ¡b := by
  cases a <;> rfl
end Bool

end Hidden

-- α から β への部分関数と β から γ への部分関数の合成の概念を定義し、
-- それが期待通りの振る舞いをすることを示すこと

def compose (f : α → Option β) (g : β → Option γ) : α → Option γ :=
  fun a : α =>
    match (f a : Option β) with
    | none   => none
    | some b => g b

example (f : α → Option β) : compose f (@Option.some β) = f :=
  calc compose f Option.some
    _ = fun a : α =>
          match (f a : Option β) with
          | none => none
          | some b => some b := rfl
    _ = f := funext (fun x => by cases f x <;> rfl)

example (g : β → Option γ) : compose (fun _ : α => @Option.none β) g = fun _ => Option.none :=
  rfl

-- Bool と Nat が有項であること
example : Inhabited Bool := Inhabited.mk true
example : Inhabited Bool := Inhabited.mk false

example : Inhabited Nat := .mk 0

-- 2つの有項な型の直積型が有項であること
example (A : Inhabited α) (B : Inhabited β) : Inhabited (Prod α β) :=
  Inhabited.mk (A.default, B.default)

-- 有項な型への関数の型は有項であること
example (f : α → Inhabited β) : Inhabited (α → Inhabited β) :=
  .mk f

example (f : α → Inhabited β) : Inhabited (α → β) :=
  .mk (fun a => (f a).default)

namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

namespace Nat

def add (n m : Nat) : Nat :=
  match m with
  | Nat.zero   => n
  | Nat.succ m => Nat.succ (add n m)

instance : Add Nat where
  add := add

theorem add_zero (n : Nat) : n + zero = n := rfl
theorem add_succ (n m : Nat) : n + succ m = succ (n + m) := rfl

theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn n
    (show zero + zero = zero from rfl)
    (fun (n : Nat) (h : zero + n = n) => show zero + succ n = succ n from
      calc zero + succ n
        _ = succ (zero + n) := rfl
        _ = succ n          := by rw [h]
    )

theorem add_assoc (n m l : Nat) : n + m + l = n + (m + l) :=
  Nat.recOn l
    (show (n + m) + zero = n + (m + zero) from rfl)
    (fun (l : Nat) (h : n + m + l = n + (m + l)) => show n + m + succ l = n + (m + succ l) from
      calc (n + m) + succ l
        _ = succ (n + m + l)   := rfl
        _ = succ (n + (m + l)) := by rw [h]
     -- _ = n + succ (m + l)   := rfl
     -- _ = n + (m + succ l)   := rfl
    )

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn m
    (show succ n + zero = succ (n + zero) from rfl)
    (fun m (h : succ n + m = succ (n + m)) => show succ n + succ m = succ (n + succ m) from
      calc succ n + succ m
        _ = succ (succ n + m)   := rfl
        _ = succ (succ (n + m)) := by rw [h]
     -- _ = succ (n + succ m)   := rfl
    )

theorem add_comm (n m : Nat) : n + m = m + n :=
  Nat.recOn m
    (show n + zero = zero + n from
      calc n + zero
        _ = n        := rfl
        _ = zero + n := by rw [zero_add]
    )
    (fun (m : Nat) (h : n + m = m + n) => show n + succ m = succ m + n from
      calc n + succ m
        _ = succ (n + m) := rfl
        _ = succ (m + n) := by rw [h]
        _ = succ m + n   := by rw [succ_add]
    )
end Nat

inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List
def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
  rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

-- 以下の定理を証明せよ
theorem append_nil (as : List α) : append as nil = as :=
  List.recOn as
    -- `nil`のとき
    (show append nil nil = nil from rfl)
    -- `as`で成り立つとして、`cons a as`でも成り立つことを示す
    (fun (a : α) (as : List α) h => show append (cons a as) nil = (cons a as) from
      calc append (cons a as) nil
        _ = cons a (append as nil) := rfl
        _ = cons a as              := by rw [h] -- congrArg (cons a) h
    )
theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn as -- `append`は1つ目の引数に関して帰納的に定義されているから...
    -- `nil`のとき
    (show append (append nil bs) cs = append nil (append bs cs) from rfl)
    -- `as`で成り立つとして、`cons a as`でも成り立つことを示す
    (fun (a : α) (as : List α) h =>
      calc append (append (cons a as) bs) cs
        _ = append (cons a (append as bs)) cs := rfl
        _ = cons a (append (append as bs) cs) := rfl
        _ = cons a (append as (append bs cs)) := by rw [h] -- congrArg (cons a) h
     -- _ = append (cons a as) (append bs cs) := rfl
    )

open Nat
-- リストの長さを返す関数 length : {α : Type u} → List α → Nat を定義せよ。
def length (as : List α) : Nat :=
  match as with
  | nil       => zero
  | cons _ as => succ (length as)

example {α : Type u} : length (@List.nil α) = zero := rfl

-- それが期待通りに振る舞うことを証明せよ。
-- 例えば、length (append as bs) = length as + length bs を証明せよ。
example (as bs : List α) : length (append as bs) = length as + length bs :=
  List.recOn as
    (show length (append nil bs) = length nil + length bs from
      calc length (append nil bs)
        _ = length bs              := rfl
        _ = zero + length bs       := by rw [Nat.zero_add] -- (Nat.zero_add (length bs)).symm
     -- _ = length nil + length bs := rfl
    )
    (fun a as h => show length (append (cons a as) bs) = length (cons a as) + length bs from
      calc length (append (cons a as) bs)
        _ = length (cons a (append as bs))   := rfl
        _ = Nat.succ (length (append as bs)) := rfl
        _ = Nat.succ (length as + length bs) := by rw [h] -- congrArg Nat.succ h
        _ = Nat.succ (length as) + length bs := by rw [Nat.succ_add] -- (Nat.succ_add ..).symm
     -- _ = length (cons a as) + length bs   := rfl
    )
end List

-- 1.
open Nat

-- 自然数に対する他の演算、例えば乗法、前者関数(pred 0 = 0 とする)、切り捨て減法(m が n以上のとき n - m = 0)、べき乗などを定義してみよ。
-- 次に、既に証明した定理を基に、それらの基本的な性質をいくつか証明してみよ。

-- 前者関数
def pred (n : Nat) : Nat :=
  match n with
  | zero   => zero
  | succ n => n

example : pred zero = zero := rfl
example : pred (succ zero) = zero := rfl

example : ∀ n : Nat, pred (succ n) = n :=
  fun _ => rfl

-- 乗法
def mul (n m : Nat) : Nat :=
  match m with
  | zero   => zero
  | succ m => add n (mul n m)

instance : Mul Nat where
  mul := mul

theorem mul_zero : ∀n, n * zero = zero :=
  fun _ => rfl
theorem succ_mul (n m : Nat) : (succ n) * m = n * m + m :=
  Nat.recOn m
    (show (succ n) * zero = n * zero + zero from rfl)
    (fun m h => show (succ n) * (succ m) = n * (succ m) + (succ m) from
      calc (succ n) * (succ m)
        _ = (succ n) + (succ n) * m := rfl
        _ = (succ n) + (n * m + m)  := congrArg _ h
        _ = (succ n) + (m + n * m)  := congrArg _ (add_comm ..)
        _ = (succ n) + m + n * m    := (add_assoc ..).symm
        _ = succ (n + m) + n * m    := congrArg (· + n * m) (succ_add n m)
        _ = n + succ m + n * m      := congrArg (· + n * m) rfl
        _ = n + (succ m + n * m)    := add_assoc ..
        _ = n + (n * m + succ m)    := congrArg _ (add_comm ..)
        _ = n + n * m + succ m      := (add_assoc ..).symm
     -- _ = n * succ m + succ m     := rfl
    )

theorem zero_mul : ∀n, zero * n = zero :=
  fun n =>
    Nat.recOn n
      (show zero * zero = zero from rfl)
      (fun n h => show zero * (succ n) = zero from
        calc zero * (succ n)
          _ = add zero (zero * n) := rfl
          _ = add zero zero       := by rw [h] -- congrArg _ h
       -- _ = zero                := rfl
      )

theorem mul_comm (n m : Nat) : n * m = m * n :=
  Nat.recOn m
    (show n * zero = zero * n from
      calc n * zero
        _ = zero     := mul_zero n
        _ = zero * n := (zero_mul n).symm
    )
    (fun m h => show n * (succ m) = (succ m) * n from
      calc n * (succ m)
        _ = n + n * m    := rfl
        _ = n + m * n    := congrArg _ h
        _ = m * n + n    := add_comm ..
        _ = (succ m) * n := (succ_mul ..).symm
    )

theorem left_distrib (n m l: Nat) : n * (m + l) = n * m + n * l :=
  Nat.recOn l
    (show n * (m + zero) = n * m + n * zero from rfl
      -- calc n * (m + zero)
      --   _ = n * m            := rfl
      --   _ = n * m + zero     := rfl
      --   _ = n * m + n * zero := rfl
    )
    (fun l h => show n * (m + succ l) = n * m + n * succ l from
      calc n * (m + succ l)
        _ = n * succ (m + l)    := rfl
        _ = n + n * (m + l)     := rfl
        _ = n + (n * m + n * l) := congrArg _ h
        _ = n + n * m + n * l   := (add_assoc ..).symm
        _ = n * m + n + n * l   := congrArg (· + n * l) (add_comm ..)
        _ = n * m + (n + n * l) := add_assoc ..
        _ = n * m + n * succ l  := congrArg _ rfl
    )

theorem mul_assoc (n m l : Nat) : n * m * l = n * (m * l) :=
  Nat.recOn l
    (show n * m * zero = n * (m * zero) from rfl)
    (fun l h => show n * m * (succ l) = n * (m * succ l) from
      calc n * m * (succ l)
        _ = n * m + n * m * l   := rfl
        _ = n * m + n * (m * l) := congrArg _ h
        _ = n * (m + m * l)     := (left_distrib ..).symm
     -- _ = n * (m * succ l)    := rfl
    )

-- 切り捨て減法
def sub (n m : Nat) : Nat :=
  match n with
  | zero   => zero
  | succ t =>
      match m with
      | zero   => n
      | succ m => sub t m

instance : Sub Nat where
  sub := sub

example : zero - zero = zero := rfl
example : zero - succ zero = zero := rfl
example : succ zero - succ zero = zero := rfl

theorem sub_self (n : Nat) : n - n = zero :=
  Nat.recOn n
    (show zero - zero = zero from rfl)
    (fun n h => show succ n - succ n = zero from
      calc succ n - succ n
        _ = n - n := rfl
        _ = zero := h
    )

theorem sub_self_add (n m : Nat) : n - (n + m) = zero :=
  Nat.recOn n
    (show zero - (zero + m) = zero from rfl)
    (fun n h => show succ n - (succ n + m) = zero from
      calc succ n - (succ n + m)
        _ = succ n - succ (n + m) := congrArg _ (succ_add ..)
        _ = n - (n + m)           := rfl
        _ = zero                  := h
    )

end Hidden

-- 2.
namespace Hidden
open Nat
open List

-- リストに関する length 関数や reverse 関数のような操作をいくつか定義せよ。
-- lengthは本文中の練習問題で定義済み。
def reverse (as : List α) : List α :=
  match as with
  | nil       => nil
  | cons a as => append (reverse as) (cons a nil)

-- それらについて、次のような性質をいくつか証明せよ。
theorem length_append (s t : List α) : length (append s t) = length s + length t :=
  List.recOn s
    (show length (append nil t) = length nil + length t from
      calc length (append nil t)
        _ = length t              := rfl
        _ = zero + length t       := (Nat.zero_add _).symm
     -- _ = length nil + length t := rfl
    )
    (fun a as h => show length (append (cons a as) t) = length (cons a as) + length t from
      calc length (append (cons a as) t)
        _ = length (cons a (append as t)) := rfl
        _ = succ (length (append as t))   := rfl
        _ = succ (length as + length t)   := congrArg _ h
        _ = succ (length as) + length t   := (Nat.succ_add ..).symm
     -- _ = length (cons a as) + length t := rfl
    )

theorem length_append_cons_nil (a : α) (as : List α) : length (append as (cons a nil)) = length (cons a as) :=
  calc length (append as (cons a nil))
    _ = length as + length (cons a nil) := length_append ..
    _ = length (cons a nil) + length as := add_comm ..
    _ = length (append (cons a nil) as) := (length_append ..).symm
    _ = length (cons a (append nil as)) := congrArg _ (cons_append ..)
    _ = length (cons a as)              := congrArg _ (nil_append ..)

example (t : List α) : length (reverse t) = length t :=
  List.recOn t
    (show length (reverse nil) = length nil from rfl)
    (fun a as h => show length (reverse (cons a as)) = length (cons a as) from
      calc length (reverse (cons a as))
        _ = length (append (reverse as) (cons a nil)) := rfl
        _ = length (reverse as) + length (cons a nil) := length_append ..
        _ = length as + length (cons a nil)           := congrArg _ h
        _ = length (append as (cons a nil))           := (length_append ..).symm
        _ = length (cons a as)                        := length_append_cons_nil ..
    )

theorem reverse_append (s t : List α) : reverse (append s t) = append (reverse t) (reverse s) :=
  List.recOn s
    (show reverse (append nil t) = append (reverse t) (reverse nil) from
      calc reverse (append nil t)
        _ = reverse t              := nil_append ..
        _ = append (reverse t) nil := (append_nil _).symm
    )
    (fun a as h => show reverse (append (cons a as) t) = append (reverse t) (reverse (cons a as)) from
      calc reverse (append (cons a as) t)
        _ = reverse (cons a (append as t))                        := rfl
        _ = append (reverse (append as t)) (cons a nil)           := rfl
        _ = append (append (reverse t) (reverse as)) (cons a nil) := congrArg (append · _) h
        _ = append (reverse t) (append (reverse as) (cons a nil)) := append_assoc ..
     -- _ = append (reverse t) (reverse (cons a as))              := rfl
    )

example (t : List α) : reverse (reverse t) = t :=
  List.recOn t
    (show reverse (reverse nil) = nil from rfl)
    (fun a as h => show reverse (reverse (cons a as)) = cons a as from
      calc reverse (reverse (cons a as))
        _ = reverse (append (reverse as) (cons a nil)) := rfl
        _ = append (reverse (cons a nil)) (reverse (reverse as)) := reverse_append ..
        _ = append (reverse (cons a nil)) as := congrArg _ h
     -- _ = append (append (reverse nil) (cons a nil)) as := rfl
     -- _ = append (append nil (cons a nil)) as := rfl
     -- _ = append (cons a nil) as := rfl
     -- _ = cons a (append nil as) := rfl
     -- _ = cons a as := rfl
    )

end Hidden

/-
以下のコンストラクタから構築される項からなる帰納データ型を定義せよ:

* `const n`, 自然数 n を表す定数
* `var n`, n 番目の変数
* `plus s t`, s と t の和を表す
* `times s t`, s と t の積を表す
-/
inductive Expr (vars : List Nat)
  | const (n : Nat)
  | var : (n : Fin vars.length) → Expr vars
  | plus (s t : Expr vars)
  | times (s t : Expr vars)
  deriving Repr

namespace Expr

-- 今定義した型の項を評価する関数を再帰的に定義せよ。ただし、変数には値を割り当てることができるとする。
def eval (vars : List Nat) (e : Expr vars) : Nat :=
  match e with
  | const n => n
  | var n => vars.get n
  | plus s t => eval vars s + eval vars t
  | times s t => eval vars s * eval vars t

theorem eval_const {vars : List Nat} (n : Nat) : eval vars (Expr.const n) = n :=
  rfl
theorem eval_var_0 {v : Nat} : eval [v] (Expr.var (Fin.ofNat 0)) = v :=
  rfl
theorem eval_plus_cc {vars : List Nat} (n m : Nat) : eval vars (Expr.plus (Expr.const n) (Expr.const m)) = n + m :=
  rfl
theorem eval_times_cc {vars : List Nat} (n m : Nat) : eval vars (Expr.times (Expr.const n) (Expr.const m)) = n * m :=
  rfl

end Expr

-- 同様に、命題論理式の型と、その型に関する関数を定義せよ:
-- 例えば、評価関数、式の複雑さを測る関数、与えられた変数に別の式を代入する関数などを定義せよ。
/-- 命題論理式 -/
inductive MyProp (vars : List Bool)
  | F
  | T
  | P (n : Fin vars.length) -- Pₙ
  | And (p q : MyProp vars)
  | Or (p q : MyProp vars)
  | Not (p : MyProp vars)

namespace MyProp
/-- 評価関数 -/
def eval (vars : List Bool) (p : MyProp vars) : Bool :=
  match p with
  | F       => false
  | T       => true
  | P n     => vars.get n
  | And p q => eval vars p && eval vars q
  | Or p q  => eval vars p || eval vars q
  | Not p   => ! eval vars p

/--
式の複雑さを測る関数

最もネストの深いところの深さを複雑さとする。
-/
def complexity {vars : List Bool} (p : MyProp vars): Nat :=
  match p with
  | And p q => 1 + max (complexity p) (complexity q)
  | Or p q  => 1 + max (complexity p) (complexity q)
  | Not p   => 1 + complexity p
  | _       => 1

example {vars : List Bool} : complexity (vars := vars) MyProp.F = 1 := rfl
example {vars : List Bool} : complexity (vars := vars) (MyProp.And (MyProp.T) (MyProp.F)) = 2 := rfl

/-- 与えられた変数に別の式を代入する関数 -/
def assign {vars : List Bool} (p : MyProp vars) (n : Fin vars.length) (q : MyProp vars) : MyProp vars :=
  match p with
  | P m     => cond (n == m) q (P m)
  | And r s => And (assign r n q) (assign s n q)
  | Or r s  => Or (assign r n q) (assign s n q)
  | Not r   => Not (assign r n q)
  | (p : _) => p

example : assign (vars := [True, False])
                 (P (Fin.ofNat 0))
                 (Fin.ofNat 0) T = T :=
  rfl

theorem assignable_prop {vars : List Bool} (n : Fin vars.length) {p : MyProp vars}
                        : assign (P n) n p = p :=
  calc assign (P n) n p
    _ = cond (n = n) p (P n) := rfl
    _ = cond true p (P n)    := congrArg (cond · _ _) (of_decide_eq_self_eq_true _)
 -- _ = p                    := rfl

theorem not_assignable_prop {vars : List Bool} {n m : Fin vars.length} {p : MyProp vars}
                            : m ≠ n → assign (vars := vars) (P n) m p = P n :=
  fun hne =>
    calc assign (P n) m p
      _ = cond (m = n) p (P n) := rfl
      _ = cond false p (P n)   := congrArg (cond · _ _) (decide_eq_false hne)
   -- _ = P n                  := rfl

example (vars : List Bool := [True, False]) (h : vars.length > 0)
        (zero := Fin.ofNat' 0 h) (one := Fin.ofNat' 1 h) -- 略記
        (hne : zero ≠ one)                               -- 面倒なのでそういうものとする...
        : assign (And (P zero) (P one)) zero F = And F (P one) :=
  calc assign (And (P zero) (P one)) zero F
    _ = And (assign (P zero) zero F) (assign (P one) zero F) := rfl
    _ = And F (assign (P one) zero F)                        := congrArg (And · _) (assignable_prop _)
    _ = And F (P one)                                        := congrArg _ (not_assignable_prop hne)

end MyProp
