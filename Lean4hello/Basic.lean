def hello := "world"

/-
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
-/

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

namespace exercise

variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => ⟨h.right, h.left⟩)
    (fun h : q ∧ p => ⟨h.right, h.left⟩)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      h.elim Or.inr Or.inl
      -- h.elim (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq)
    )
    (fun h : q ∨ p =>
      h.elim Or.inr Or.inl
      -- h.elim (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp)
    )

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (fun h : p ∧ (q ∧ r) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      h.elim
        (fun h : p ∨ q => h.elim Or.inl (Or.inr ∘ Or.inl))
        (fun h : r => (Or.inr ∘ Or.inr) h))
    (fun h : p ∨ (q ∨ r) =>
      h.elim
        (fun h : p => (Or.inl ∘ Or.inl) h)
        (fun h : (q ∨ r) => h.elim (Or.inl ∘ Or.inr) Or.inr))

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      h.right.elim
        (Or.inl ∘ And.intro hp) -- （hq : qを貰って、）hp（とhq）からp ∧ qを作ったら、それは結論の左だ
        (Or.inr ∘ And.intro hp) -- （hr : rを貰って、）hp（とhr）からp ∧ rを作ったら、それは結論の右だ
    )
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      h.elim
        (fun h : p ∧ q => ⟨h.left, Or.inl h.right⟩)
        (fun h : p ∧ r => ⟨h.left, Or.inr h.right⟩)
    )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from
      h.elim
        (fun h : p => ⟨Or.inl h, Or.inl h⟩)
        (fun h : q ∧ r => ⟨Or.inr h.left, Or.inr h.right⟩)
    )
    (fun h : (p ∨ q) ∧ (p ∨ r) => show p ∨ (q ∧ r) from
      h.left.elim
        (fun hp => Or.inl hp)
        (fun hq => h.right.elim Or.inl (Or.inr ∘ And.intro hq))
    )

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) => fun hpq : p ∧ q => show r from h hpq.left hpq.right)
    (fun h : p ∧ q → r => fun hp : p => fun hq : q => show r from h ⟨hp, hq⟩)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : ((p ∨ q) → r) => show (p → r) ∧ (q → r) from
      And.intro
        (show p → r from fun hp : p => show r from h (Or.inl hp))
        (show q → r from fun hq : q => show r from h (Or.inr hq))
    )
    (fun h : (p → r) ∧ (q → r) => show (p ∨ q) → r from
      fun hpq : p ∨ q => show r from
        hpq.elim
          (show p → r from h.left)
          (show q → r from h.right)
    )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) => show ¬p ∧ ¬q from
      And.intro
        (
          show ¬p from
          show p → False from
          fun hp => h (Or.inl hp)
        )
        (
          show ¬q from
          show q → False from
          fun hq => h (Or.inr hq)
        )
    )
    (fun h : ¬p ∧ ¬q =>
      show ¬(p ∨ q) from
      show (p ∨ q) → False from
      fun h₁ : p ∨ q => show False from
        h₁.elim h.left h.right
    )
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h : ¬p ∨ ¬q => show ¬(p ∧ q) from
    fun hpq : p ∧ q => show False from
      h.elim (absurd hpq.left) (absurd hpq.right)
example : ¬(p ∧ ¬p) := show p ∧ ¬p → False from
  fun hpnp : p ∧ ¬p => show False from absurd hpnp.left hpnp.right
example : p ∧ ¬q → ¬(p → q) :=
  fun hpnq : p ∧ ¬q => show (p → q) → False from
    fun h : p → q => show False from absurd (h hpnq.left) hpnq.right
example : ¬p → (p → q) :=
  fun hnp : ¬p => show p → q from
    fun hp : p => show q from False.elim (absurd hp hnp)
example : (¬p ∨ q) → (p → q) :=
  fun h : ¬p ∨ q => show p → q from
    fun hp : p => show q from
      h.elim
        (show ¬p → q from False.elim ∘ absurd hp)
        (show q → q from id)
example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False => show p from
      h.elim
        (show p → p from id)
        (show False → p from False.elim))
    (show p → p ∨ False from Or.inl)
example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False => show False from h.right)
    (show False → p ∧ False from False.elim)
example : (p → q) → (¬q → ¬p) :=
  fun hp2q : p → q => show (q → False) → (p → False) from
    fun hnq : q → False => show p → False from
      fun hp : p => show False from hnq (hp2q hp)

section withClassical
open Classical

variable (p q r : Prop)

def dne := @classical.my_dne

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r => show (p → q) ∨ (p → r) from
    Or.elim (em q) -- q ∨ ¬q
      (fun hq : q => Or.inl (show p → q from fun _ => hq))
      (fun hnq : ¬q => Or.inr (show p → r from
          fun hp : p => Or.elim (h hp) -- q ∨ r
            (show q → r from fun hq => absurd hq hnq)
            (show r → r from id)
        )
      )
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : p ∧ q → False => show (p → False) ∨ (q → False) from
    Or.elim (em q) -- q ∨ ¬q
      (fun hq : q => Or.inl (show p → False from fun hp : p => h ⟨hp, hq⟩))
      (show ¬q → _ ∨ ¬q from Or.inr)
example : ¬(p → q) → p ∧ ¬q :=
  fun h : (p → q) → False => show p ∧ ¬q from
    Or.elim (em p) -- p ∨ ¬p
      (fun hp : p => ⟨hp, fun hq : q => h (fun _ => hq)⟩)
      (fun hnp : ¬p => And.intro
        (show p from False.elim (h (fun hp => absurd hp hnp)))
        (show q → False from fun hq => show False from h (fun _ => hq)))
example : (p → q) → (¬p ∨ q) :=
  fun h : p → q => show ¬p ∨ q from
    Or.elim (em p) -- p ∨ ¬p
      (show p → _ ∨ q from Or.inr ∘ h)
      (show ¬p → ¬p ∨ _ from Or.inl ∘ id)
example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p => show p → q from
    fun hp : p => show q from
      -- ¬¬q ≡ ¬q → False
      dne (fun hnq : ¬q => show False from absurd hp (h hnq))
example : p ∨ ¬p := em p
example : (((p → q) → p) → p) :=
  fun h : (p → q) → p => show p from
    byContradiction
      fun hnp : ¬p => show False from
        hnp (h (fun hp => absurd hp hnp))
end withClassical

example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p => show False from
    have hp : p := (h.mpr (fun hp => absurd hp (h.mp hp)))
    (h.mp hp) hp

end exercise
