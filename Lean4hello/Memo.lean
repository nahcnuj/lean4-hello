namespace simple_type_theory
/- 項の定義 -/
def n : Nat := 42
def b1 : Bool := true
def b2 : Bool := false

/- 項の型のチェック -/
#check n        -- : Nat
#check b1 && b2 -- : Bool
#check b1 || b2 -- : Bool

/- 項を評価する -/
#eval 5 * 4    -- 20
#eval n + 2    -- 44
#eval b1 && b2 -- false

/-
  ブロックコメント
  /- 入れ子 -/
-/

#check Nat -> Nat -- NatからNatへの関数
#check Nat → Nat  -- `\to`

#check Nat × Nat    -- ×は`\times`で入力
#check Prod Nat Nat -- ASCIIで書くなら

#check Nat -> Nat -> Nat
#check Nat -> (Nat -> Nat) -- `->`は右結合
#check Nat × Nat -> Nat

#check (Nat -> Nat) -> Nat -- `Nat -> Nat`の関数を受け取る

#check Nat.succ -- : Nat -> Nat
#check (0, 1)   -- : Nat × Nat
#check Nat.add  -- : Nat -> Nat -> Nat

#check Nat.succ 2 -- : Nat
#eval  Nat.succ 2 -- 3

#check Nat.add 3  -- : Nat -> Nat

#check Nat.add 5 2 -- : Nat
#eval  Nat.add 5 2 -- 7

#check (5, 9).1 -- : Nat
#check (5, 9).2 -- : Nat
#eval  (5, 9).1 -- 5
#eval  (5, 9).2 -- 9

#eval Nat.add (10, 7).1 (10, 7).2 -- 17

end simple_type_theory

namespace types_as_objects /- 項としての型 -/
#check Nat        -- : Type
#check Bool       -- : Type
#check Nat → Bool -- : Type

def α : Type := Nat
def β : Type := Bool
def F : Type -> Type := List
def G : Type -> Type -> Type := Prod

#check α     -- : Type
#check F α   -- : Type
#check F Nat -- : Type
#check G α   -- : Type -> Type
#check G α β -- : Type

#check List α   -- 型αの項からなるリストの型
#check List Nat

/- 型の階層 -/
#check Type   -- : Type 1
#check Type 1 -- : Type 2
#check Type 2 -- : Type 3

#check Type 0 -- Type : Type 1

#check List -- : Type u → Type u
#check Prod -- : Type u → Type v → Type (max u v)

/-
universe u -- 宇宙変数
def f (α : Type u) : Type u := Prod α α -- `Type u`に属する型 α を受け取って、直積型 α × α を返す関数
#check f -- Type u → Type u

def g.{v} (α : Type v) : Type v := Prod α α -- `.{u}` で宇宙レベルを指定するやり方
#check g
-/

end types_as_objects

namespace fun_abst_and_eval
/- 関数 fun または λ -/
#check fun (x : Nat) => x + 5 -- Nat → Nat
#eval (λ x : Nat => x + 5) 10 -- 15

-- 引数の型推論
#check fun x y => if not y then x + 1 else x + 2 -- : Nat → Bool → Nat

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x       -- : Nat → Nat
#check fun x : Nat => true    -- : Nat → Bool
#check fun x : Nat => g (f x) -- : Nat → Bool
#check fun x => g (f x)

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

#check (fun (α β γ : Type) (G : β → γ) (F : α → β) (x : α) => G (F x)) Nat String Bool g f 0
-- : Bool
#eval  (fun (α β γ : Type) (G : β → γ) (F : α → β) (x : α) => G (F x)) Nat String Bool g f 0
-- true
end fun_abst_and_eval

namespace defs
/- 定義 -/
def double (x : Nat) : Nat := x + x
#eval double 3 -- 6

-- 名前付きのラムダ抽象として
def double₁ : Nat → Nat := fun x => x + x
#eval double₁ 3 -- 6

-- 型推論
def double₂ := fun x : Nat => x + x

def pi := 3.141592654
#check pi -- : Float

def add (x y : Nat) := x + y
#eval add 3 2 -- 5
#eval add (double 3) (7 + 9) -- 22

def greater (x y : Nat) := if x > y then x else y
#eval greater 3 2    -- 3
#eval greater 99 100 -- 100
#eval greater 5 5    -- 5

def square (x : Nat) := x * x

def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

#eval doTwice double 2 -- 8
#eval doTwice square 3 -- 81

def compose (α β γ : Type) (g : β → γ) (f : α → β) : α → γ := fun x : α => g (f x)

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0
#check compose Nat String Bool g f -- : Nat → Bool

#eval compose Nat Nat Nat double square 3 -- 18 = 3² + 3²
#eval compose Nat Nat Nat square double 3 -- 36 = (3 + 3)²

end defs

namespace local_defs
/- ローカルな定義 -/
def double_square (x : Nat) : Nat :=
  let y := x + x; y * y
-- `double_square x`は項`(x + x) * (x + x)`とdefinitionally equal

#check double_square 2 -- : Nat
#eval  double_square 2 -- 16

def foo :=
  let a := Nat
  fun x : a => x + 2

/-
def bar :=
  (fun a => fun x : a => x + 2) Nat
-/
end local_defs

namespace vars_and_sections

variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def doTwice (h : α → α) (x : α) : α := h (h x)
def doThrice (h : α → α) (x : α) : α := h (h (h x))

#print compose
#print doTwice
#print doThrice

end vars_and_sections

namespace dependency
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons      -- : (α : Type) → α → List α → List α
#check cons Nat  -- : Nat → List Nat → List Nat
#check cons Bool -- : Bool → List Bool → List Bool

#check @List.cons   -- : {α : Type u_1} → α → List α → List α
#check @List.nil    -- : {α : Type u_1} → List α
#check @List.length -- : {α : Type u_1} → List α → Nat
#check @List.append -- : {α : Type u_1} → List α → List α → List α

/-
依存関数型`(a : α) → β a`：`α → β`の一般化
依存積型`(a : α) × β a`：`α × β`の一般化

`(a : α) × β a`は`Σ a : α, β : a`とも
-/

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

#print f
#print g -- fと同じ

#check f Type (fun α => α) Nat 2

def h (x : Nat) := f Type (fun α => α) Nat x
#check h 5
#check (h 5).1 -- : Type
#eval  (h 5).2 -- 5 : Nat

def i : Type := (h 5).1
-- iは`Nat`型を指す

def test : i := 5 + 5
#eval test
end dependency

namespace imp_args
#check List.nil
#check (List.nil : List Nat) -- : List Nat

#check id
#check (id : Nat → Nat) -- : Nat → Nat

#check 2         -- : Nat
#check (2 : Nat) -- : Nat
#check (2 : Int) -- : Int

#check @id      -- : {α : Sort u_1} → α → α
#check @id Nat  -- : Nat → Nat
#check @id Bool -- : Bool → Bool

#check @id Nat 1     -- : Nat
#check @id Bool true -- : Bool
end imp_args

namespace props_as_types
def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

structure Proof (p : Prop) : Type where
  proof : p

-- 公理：`Proof p`のような型を持つ定数（ただし`p : Prop`）

-- Andの交換則
axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

-- モーダス・ポネンス
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

-- 含意導入
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

/-
ある式`t`が命題`p : Prop`の正しい証明である
<= `t`が`Proof p`の型を持つことを示せば良い

命題`p : Prop`があるとき、`p`自体を型として解釈できる。
そして型`p`を証明の型（`Proof p`）と解釈し、これらを同一視する。
すると、「式`t`が命題`p`の証明である」を`t : p`と書ける。

`Implies p q`は`p → q`と同一視できる。

`p`の証明＝正しく型付けされた項`t : p`
-/

/-
命題`p`に対して、`p`が偽なら空の型を関連付け、`p`が真ならただ一つの項`*`を持つ型を関連付ける。
`p`が真のとき、`p`に関連付けられた型を inhabited (有項) と呼び、それが持つ項`*`を inhabitant (住人) と呼ぶ。
-/

/-
依存型理論の言語において、
数学的な命題`p`を形式的に表現する＝項`p : Prop`を構築する
命題`p`を「証明」する＝項`t : p`を証明する
-/

variable {p q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
#print t1 -- 定理の証明を表示する

axiom t0 : False -- 公理＝与えられた型の項の存在を無条件に認める
theorem ex : 1 = 0 := -- 本来は偽の命題だが
  False.elim t0       -- 示せてしまった（爆発律）

variable {α β : Type}
def f1 : α → β → α := fun hp : α => fun hq : β => hp
#print f1

theorem t2 : ∀ {p q : Prop}, p → q → p := fun {p q : Prop} (hp : p) (hq : q) => hp
#print t2 -- t1と同じ

-- p,qを必須引数にして様々な例を作る
theorem t3 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)
#check t3 p q -- : p → q → p
#check t3 r s -- : r → s → r
#check t3 (r → s) (s → r) -- : (r → s) → (s → r) → r → s -- `→`は右結合だから最後のカッコが省略されている

variable (h : r → s)
#check t3 (r → s) (s → r) h -- : (s → r) → r → s

theorem t4 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
#print t4
end props_as_types

namespace prop_logic
variable (p q : Prop)

#check (p → (q → (p ∧ q)))
#check (((¬p) → p) ↔ False)
#check ((p ∨ q) → (q ∨ p))

-- 連言 conjunction
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp : p) (hq : q) => And.intro hp hq
-- fun hp hq => { left := hp, right := hq } : p → q → p ∧ q

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)

#check List.length xs
#check xs.length

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

example (h : p ∧ q) : q ∧ (p ∧ q) := ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩ -- 右結合
example (h : p ∧ q) : (q ∧ p) ∧ q := ⟨⟨h.right, h.left⟩, h.right⟩

-- 選言 disjunction
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

#check Or.intro_left  -- Or.intro_left {a : Prop} (b : Prop) (h : a) : a ∨ b
#check Or.intro_right -- Or.intro_right {b : Prop} (a : Prop) (h : b) : a ∨ b

example (h : p ∨ q) : q ∨ p :=
  -- `p ∨ q`の∨を外して...
  Or.elim h
    -- 左`p`から結論`q ∨ p`を示す
    (fun hp : p => show q ∨ p from Or.intro_right _ hp)
    -- 右`q`から結論`q ∨ p`を示す
    (fun hq : q => show q ∨ p from Or.intro_left _ hq)

-- いろいろ略せる
example (h : p ∨ q) : q ∨ p :=
  h.elim
    (fun hp => Or.inr hp) -- `Or.inr` = `Or.intro_right _`
    (fun hq => Or.inl hq) -- `Or.inl` = `Or.intro_left _`

-- 否定 negation と 恒偽 falsity

#print Not -- def Not : Prop → Prop := fun a => a → False

-- (p → q) → ¬q → ¬p
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  -- `¬p` = `p → False` だから...
  fun (hp : p) => show False from hnq (hpq hp)
  -- `False`を示すために、`hnq : q → False`を使うために、`q`を`hpq : p → q`と`hp : p`から得る

-- 爆発律
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := @False.elim q (hnp hp)

#check False.elim -- : {C : Sort u} → False → C
-- False を渡せば任意の型を得られる

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
#check absurd -- : {a : Prop} → {b : Sort v} → a → ¬a → b

-- ¬p → q → (q → p) → r
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

-- 論理同値 logical equivalence
example (hpq : p → q) (hqp : q → p) : p ↔ q := Iff.intro hpq hqp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    -- p ∧ q → q ∧ p
    (fun h : p ∧ q => show q ∧ p from ⟨h.right, h.left⟩)
    -- q ∧ p → p ∧ q
    (fun h : q ∧ p => show p ∧ q from ⟨h.right, h.left⟩)

#check and_swap p q -- : p ∧ q ↔ q ∧ p

-- `Iff.mp h` : `h : p ↔ q`から`p → q`の証明を作る
example (h : p ∧ q) : q ∧ p :=
  Iff.mp
    (and_swap p q) -- p ∧ q ↔ q ∧ p
    h              -- p ∧ q

-- have で補助ゴール
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

-- suffices で「Aを示すにはBを示せば十分」
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  -- `q`を示せば良い。∵`hq : q`を仮定すれば結論が得られる
  suffices hq : q from ⟨hq, hp⟩
  show q from h.right -- `q` であることを示す

end prop_logic

namespace classical
open Classical

variable (p : Prop)

-- 二重否定の除去 ¬¬p → p
theorem my_dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p) -- 排中律 p ∨ ¬p
    --  p → p
    (fun hp : p => hp)
    -- ¬p → p
    (fun hnp : ¬p => absurd hnp h) -- ¬p と ¬(¬p) から（任意の命題）p

/-
-- 証明図に基づく： https://www.ne.jp/asahi/search-center/internationalrelation/mathWeb/meidai/syntaxPrpsNKDNEtoLEM.htm
theorem em (p : Prop) : p ∨ ¬p :=
  have h₁ : p → p ∨ ¬p := fun hp => Or.inl hp
  have h₂ : p → ¬(p ∨ ¬p) → False := fun hp => fun h => absurd (h₁ hp) h
  have h₃ : ¬(p ∨ ¬p) → ¬p := fun h => byContradiction fun hn => h₂ (my_dne hn) h
  have h₄ : ¬(p ∨ ¬p) → p ∨ ¬p := fun h => Or.inr (h₃ h)
  have h₅ : ¬(p ∨ ¬p) → False := fun h => absurd (h₄ h) h
  byContradiction h₅
-/

/-
-- https://proofassistants.stackexchange.com/questions/1856/lean4-exercise-double-negation-implies-law-of-excluded-middle
theorem my_em (p : Prop) : p ∨ ¬p :=
  my_dne (fun h => h (Or.inr (fun hp => h (Or.inl hp))))
-/

theorem my_em (p : Prop) : p ∨ ¬p :=
  my_dne (
    show ¬¬(p ∨ ¬p) from
    show ¬(p ∨ ¬p) → False from
      fun h : ¬(p ∨ ¬p) => (
        show False from
          h (
            show p ∨ ¬p from
            show p ∨ (p → False) from
              Or.inr (
                show ¬p from
                show p → False from
                  fun hp : p => (
                    show False from
                      h (
                        show p ∨ ¬p from
                          Or.inl hp
                      )
                  )
              )
          )
      )
  )
end classical

namespace quantifiers_and_equality

/-
`p : α → Prop`：型`α`上の一変数述語
`p x`：`x : α`に対して`p`が成り立つという主張

`r : α → α → Prop`：型`α`上の二項関係

`∀ x : α, p x`

- `x : α`が自由に選べる文脈で`p x`の証明が与えられたら、`∀ x : α, p x`の証明を作れる
- `∀ x : α, p x`の証明があるとき、任意の項`t : α`に対して`p t`の証明が得られる

- `x : α`が自由に選べる文脈で型`β x`の項`t`が作れるなら、`(fun x : α => t) : (x : α) → β x`が作れる
- 与えられた項`s : (x : α) → β x`から、任意の項`t : α`に対して項`s t : β t`が得られる

`p x : Prop`のとき、型`(x : α) → β x`を型`∀ x : α, p x`と同一視することで、
上記をそれぞれ同一視できる
-/

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x => show ∀ y : α, p y from
    fun y : α => show p y from -- `y`を任意に取る
      have hpq : p y ∧ q y := h y -- 仮定から
      hpq.left

-- R：α上の二項関係
variable (α : Type) (R : α → α → Prop)
-- Rは推移的（x R y かつ y R z なら x R z）
variable (trans_r : ∀ x y z : α, R x y → R y z → R x z)

-- 任意のa,b,c : αに対して
variable (a b c : α)
-- a R b かつ b R c とすると...
variable (hab : R a b) (hbc : R b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc -- ... a R c が成り立つ、という主張

-- 省略
variable (trans_r2 : ∀ {x y z}, R x y → R y z → R x z)

#check trans_r2        -- : R ?m.2415 ?m.2416 → R ?m.2416 ?m.2417 → R ?m.2415 ?m.2417
#check trans_r2 hab    -- : trans_r2 hab : R b ?m.2469 → R a ?m.2469
#check trans_r2 hab hbc -- : R a c

variable (Req : α → α → Prop)
variable (refl_Req : ∀ x, Req x x)
variable (symm_Req : ∀ {x y}, Req x y → Req y x)
variable (trans_Req : ∀ {x y z}, Req x y → Req y z → Req x z)

-- ∀ a b c d : α, (a R₌ b) ∧ (c R₌ b) ∧ (c R₌ d) → a R₌ d
example (a b c d : α) (hab : Req a b) (hcb : Req c b) (hcd : Req c d) : Req a d :=
  trans_Req
    (show Req a c from trans_Req hab (symm_Req hcb))
    (show Req c d from hcd)

-- 等号
universe u v
#check @Eq.refl.{u} -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u} -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u} -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

variable (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d :=
  Eq.trans (Eq.trans hab hcb.symm) hcd

variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
-- (fun x => f x) ≡ f を簡約して同一視してくれる
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
-- (a, b).1 ≡ a を簡約して同一視してくれる
-- (a, b) : α × β
example : 2 + 3 = 5 := Eq.refl _
-- 計算して同一視してくれる

#check @Eq.subst.{u} -- @Eq.subst : ∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a → motive b

variable (α : Type) (a b : α) (p : α → Prop)
example (hab : a = b) (hpa : p a) : p b :=
  Eq.subst hab hpa
example (hab : a = b) (hpa : p a) : p b :=
  hab.subst hpa
example (hab : a = b) (hpa : p a) : p b :=
  hab ▸ hpa -- `▸`は`\t`で入力できる
example (hab : a = b) (hpb : p b) : p a :=
  hab ▸ hpb -- 左（b）を右（a）に置き換えるのも同じ書き方でやってくれる

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁ -- 引数の方に等号を適用
example : f a = g a := congrFun h₂ a -- 関数の方に等号を適用
example : f a = g b := congr h₂ h₁   -- 両方に等号を適用

#check @congrArg.{u, v}
-- @congrArg : ∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂
#check @congrFun.{u, v}
-- @congrFun : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g → ∀ (a : α), f a = g a
#check @congr.{u, v}
-- @congr : ∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ → a₁ = a₂ → f₁ a₁ = f₂ a₂

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h₁ : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.left_distrib (x + y) x y
  have h₂ : (x + y) * x = x * x + y * x := Nat.right_distrib x y x
  have h₃ : (x + y) * y = x * y + y * y := Nat.right_distrib x y y
  have h₄ := h₃ ▸ h₂ ▸ h₁
  Nat.add_assoc _ _ _ ▸ h₄
  -- Nat.add_assoc (x * x + y * x) (x * y) (y * y) ▸ h₄

variable (x y : Nat) (h : x = y)
#check congrArg (@Nat.add (x * x)) h
#check (congrArg (fun a => a + (y * y)) (Nat.add_comm (x * y) (y * x)))

-- 計算的証明
example (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc a
    _ = b     := h1                   -- a = b
    _ = c + 1 := h2                   -- b = c + 1
    _ = d + 1 := congrArg Nat.succ h3 -- c + 1 = d + 1
    _ = 1 + d := Nat.add_comm _ _     -- d + 1 = 1 + d
    _ = e     := h4.symm              -- 1 + d = e

example (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc a
    _ = b     := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

example (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

example (a b c d e : Nat) (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]


example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc a
    _ = b     := h1                 -- a = b
    _ ≤ c     := h2                 -- b ≤ c
    _ < c + 1 := Nat.lt_succ_self _ -- c < c + 1
    _ < d     := h3                 -- c + 1 < d

def divides (x y : Nat) : Prop := ∃ k, k * x = y
def divides_trans {x y z : Nat} (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁ -- k₁ : Nat , d₁ : k₁ * x = y
  let ⟨k₂, d₂⟩ := h₂ -- k₂ : Nat , d₂ : k₂ * y = z
  ⟨k₁ * k₂, show k₁ * k₂ * x = z from
    calc k₁ * k₂ * x
      _ = k₁ * (k₂ * x) := Nat.mul_assoc _ _ _
      _ = k₂ * (k₁ * x) := Nat.mul_left_comm _ _ _
      _ = k₂ * y        := congrArg _ d₁ -- by rw [d₁]
      _ = z             := d₂
    ⟩
def divides_mul (x : Nat) (k : Nat) : divides x (k * x) := ⟨k, rfl⟩

-- `calc`に推移律の定義を教える
instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    divides x y       := h₁
    y = z             := h₂
    divides z (2 * z) := divides_mul ..

infix:50 " ∣ " => divides
example (h₁ : x ∣ y) (h₂ : y = z) : x ∣ (2 * z) :=
  calc x
    _ ∣ y     := h₁
    _ = z     := h₂
    _ ∣ 2 * z := divides_mul ..

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = x * (x + y) + y * (x + y)         := Nat.add_mul x y (x + y)
    _ = x * x + x * y + y * (x + y)       := congrArg (fun n => n + (y * (x + y))) (Nat.left_distrib ..)
    _ = x * x + x * y + (y * x + y * y)   := congrArg (Nat.add (x * x + x * y)) (Nat.left_distrib ..)
    _ = x * x + (x * y + (y * x + y * y)) := Nat.add_assoc ..
    _ = x * x + (y * x + (x * y + y * y)) := congrArg (Nat.add (x * x)) (Nat.add_left_comm (x * y) (y * x) (y * y))
    _ = x * x + y * x + (x * y + y * y)   := Eq.symm (Nat.add_assoc (x * x) (y * x) (x * y + y * y))
    _ = x * x + y * x + x * y + y * y     := Eq.symm (Nat.add_assoc (x * x + y * x) (x * y) (y * y))

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul] -- congrArg (fun n => n + _) (Nat.add_mul ..)
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul] -- congrArg (Nat.add (x * x + y * x)) (Nat.add_mul ..)
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc] -- Eq.symm (Nat.add_assoc (x * x + y * x) (x * y) (y * y))

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h -- 1 : Nat と h : 1 > 0

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h -- 0 : Nat と 0 < x

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (show x < y ∧ y < z from ⟨hxy, hyz⟩)

variable (α : Type) (p q : α → Prop)
example (h : ∃ x : α, p x ∧ q x) : ∃ x : α, q x ∧ p x :=
  h.elim
    (fun w : α => fun hw : p w ∧ q w =>
      show ∃ x : α, q x ∧ p x from ⟨w, ⟨hw.right, hw.left⟩⟩)

example (h : ∃ x : α, p x ∧ q x) : ∃ x : α, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x : α, p x ∧ q x) : ∃ x : α, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hpw : p w), (hqw : q w)⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x : α, p x ∧ q x) : ∃ x : α, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example : (h : ∃ x : α, p x ∧ q x) -> ∃ x : α, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) : Prop := ∃b : Nat, a = 2 * b

example {a b : Nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  h1.elim fun k1 => fun hk1 : a = 2 * k1 =>
  h2.elim fun k2 => fun hk2 : b = 2 * k2 =>
    ⟨k1 + k2, show a + b = 2 * (k1 + k2) from
      calc a + b
        _ = 2 * k1 + 2 * k2 := by rw [hk1, hk2]
        _ = 2 * (k1 + k2)   := by rw [Nat.mul_add]⟩

example {a b : Nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨k1, (hk1 : a = 2 * k1)⟩, ⟨k2, (hk2 : b = 2 * k2)⟩ => ⟨k1 + k2, by rw [hk1, hk2, Nat.mul_add]⟩

open Classical
-- universe u
variable (α : Sort u) (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction -- ¬(∃ x, p x) → False
    fun hc : ¬∃x, p x => show False from
      h (show ∀ (x : α), ¬p x from
        fun x : α => fun hpx : p x => show False from
          hc ⟨x, hpx⟩
      )
end quantifiers_and_equality
