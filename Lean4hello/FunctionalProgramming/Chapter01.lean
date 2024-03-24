namespace FunctionalProgramming

/-
# Chapter 1: Getting to Know Lean
-/
namespace Chapter01

/-
## 1.1 Evaluating Expressions
-/
namespace Section01

example : 42 + 19 = 61 := rfl
example : String.append "A" (String.append "B" "C") = "ABC" := rfl
example : String.append (String.append "A" "B") "C" = "ABC" := rfl
example : (if 3 == 3 then 5 else 7 : Nat) = 5 := rfl
example : (if 3 == 4 then "equal" else "not equal" : String) = "not equal" := rfl

end Section01

/-
## 1.2 Types
-/
namespace Section02

example : 1 - 2 = 0 := rfl -- `1` and `2` are values of `Nat` type
example : (1 - 2 : Int) = -1 := rfl

end Section02

/-
## 1.3 Functions and Definitions
-/
namespace Section03

def hello := "Hello"
def lean : String := "Lean"

example : String.append hello (String.append " " lean) = "Hello Lean" := rfl

/-
`def`は関数(function)を定義するのにも使われるが、
`hello`は常に同じ値を返す引数のない関数*ではない*！
その値を直接参照する名前が導入される。
-/

def add1 (n : Nat) : Nat := n + 1
-- Nat → Nat

example : add1 7 = 8 := rfl

def maximum (n : Nat) (m : Nat) : Nat :=
  if n < m then m else n

example : Nat → Nat → Nat := maximum
-- カリー化(currying)されている

example : maximum (5 + 8) (2 * 7) = 14 := rfl

/-
#check add1   -- add1 (n : Nat) : Nat
#check (add1) -- add1 : Nat → Nat
-/

def joinStringsWith (sep : String) (pre : String) (post : String) : String :=
  String.append pre (String.append sep post)

example : joinStringsWith ", " "one" "and other" = "one, and other" := rfl
example : String → String → String := joinStringsWith ": "

def volume (height : Nat) (width : Nat) (depth : Nat) : Nat :=
  height * width * depth

def Str : Type := String
def aStr : Str := "This is a string."
--         ^ 定義（`String`）で置き換えられる

def NaturalNumber := Nat

def thirtyEight : NaturalNumber := (38 : Nat)
/-
単に`38`で定義しようとすると：
```
failed to synthesize instance
  OfNat NaturalNumber 38
```
Leanでは数リテラルをオーバーロードできるが、`Nat`を`NaturalNumber`にオーバーロードするのは非自明
`38`が`Nat`型だと教えてあげれば、`NaturalNumber`は定義から`Nat`なのでOK！
-/

/-
`abbrev`を使えばオーバーロード解決も同様に名前から置き換えられる
生成される定義が簡約可能(reducible)だとマークされる
-/
abbrev ℕ : Type := Nat
def thirtyNine : ℕ := 39
-- `(39 : Nat)`としなくて良い

end Section03

/-
## 1.4 Structures
-/
namespace Section04

structure Point where
  x : Float
  y : Float
  deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

example : origin.x = 0.0 := rfl
example : origin.y = 0.0 := rfl

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
-- #eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 } -- { x := -6.500000, y := 32.200000 }

def distance (p1 p2 : Point) : Float :=
  Float.sqrt ((p2.x - p1.x) ^ 2.0 + (p2.y - p1.y) ^ 2.0)
-- #eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 } -- 5.000000

structure Point3D where
  (x y z : Float)
  deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

def p           := ({x := 0.0, y := 0.0} : Point)
def p'          := { x := 0.0, y := 0.0 : Point }
def p'' : Point := { x := 0.0, y := 0.0 }

def zeroX (p : Point) : Point :=
  { p with x := 0 }

def q : Point := { x := 4.3, y := 3.4 }
-- #eval q       -- { x := 4.300000, y := 3.400000 }
-- #eval zeroX q -- { x := 0.000000, y := 3.400000 }
-- #eval q       -- { x := 4.300000, y := 3.400000 }

example : Float → Float → Point := Point.mk
example : Point.mk 1.5 2.8 = { x := 1.5, y := 2.8 : Point } := rfl

structure Point' where
  point :: -- constructor name
  x : Float
  y : Float
  deriving Repr
example : Point'.point 1.5 2.8 = { x := 1.5, y := 2.8 : Point' } := rfl

example : origin.x = Point.x origin := rfl
example : Point → Float := Point.x

example : "one string".append " and another" = "one string and another" := rfl

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

-- #eval q.modifyBoth Float.floor -- { x := 4.000000, y := 3.000000 }

/-- 直方体 -/
structure RectangularPrism where
  height : Float
  width  : Float
  depth  : Float

/-- 直方体の体積 -/
def volume (r : RectangularPrism) : Float :=
  r.height * r.width * r.depth

/-- 平面上の線分 -/
structure Segment where
  p : Point
  q : Point

/-- 線分の長さ -/
def length (s : Segment) : Float :=
  distance s.p s.q

example : Float → Float → Float → RectangularPrism := RectangularPrism.mk
example : RectangularPrism → Float                 := RectangularPrism.height
example : RectangularPrism → Float                 := RectangularPrism.width
example : RectangularPrism → Float                 := RectangularPrism.depth

structure Hamster where
  name   : String
  fluffy : Bool -- ふわふわ
example : String → Bool → Hamster := Hamster.mk
example : Hamster → String        := Hamster.name
example : Hamster → Bool          := Hamster.fluffy

structure Book where
  makeBook ::
  title  : String
  author : String
  price  : Float
example : String → String → Float → Book := Book.makeBook -- `mk`*ではない*
example : Book → String                  := Book.title
example : Book → String                  := Book.author
example : Book → Float                   := Book.price

end Section04

/-
## 1.5 Datatypes and Patterns

product type       -- 値の組を一緒にまとめた構造、タプル、`structure`
sum type           -- 選択可能な型
recursive datatype -- 再帰的な型
inductive datatype -- recursive sum type
-/
namespace Section05

namespace Hidden
inductive Bool where
  | false : Bool -- a `Bool`'s constructor named `false`
  | true  : Bool -- a `Bool`'s constructor named `true`
example : Bool := Bool.false
example : Bool := Bool.true
end Hidden

-- structureのコンストラクタは`mk`ひとつだけだった

namespace Hidden
inductive Nat where
  | zero           : Nat -- 0
  | succ (n : Nat) : Nat -- ある数の「次の数」(successor)
example : Nat       := Nat.zero
example : Nat → Nat := Nat.succ
end Hidden

example : 4 = Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))) := rfl

/-
JavaやC#、TypeScriptで表現するならこうかな、というのが書かれていて良い...
-/

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

example : isZero Nat.zero = true := rfl
example : isZero 5 = false :=
  calc isZero 5
    _ = isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
      := rfl
    _ = match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
        | Nat.zero   => true
        | Nat.succ _ => false
      := rfl
    _ = false
      := rfl

example : Nat.pred 5 = 4 := rfl
example : Nat.pred 0 = 0 := rfl

namespace Hidden
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

example : pred (Nat.succ (Nat.succ Nat.zero)) = Nat.succ Nat.zero := rfl
example : pred Nat.zero = Nat.zero := rfl
end Hidden

export Section04 (Point3D)
def depth (p : Point3D) : Float :=
  match p with
  | { x := _, y := _, z := d } => d

def depth' (p : Point3D) : Float :=
  p.z

example (p : Point3D) : depth p = depth' p := rfl

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true         -- a base case (non-recursive branch)
  | Nat.succ k => not (even k)
-- 構造的再帰(structural recursion)

/-
Leanでは、やがてbase caseに達することがデフォルトで要請される
上の例では（`Nat.succ`の定義から）`n > k`なのでOK（いつかは`n = Nat.zero`に達する）
-/

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ (plus n k')

example : plus 3 2 = 5 :=
  calc plus 3 2
    _ = plus 3 (Nat.succ (Nat.succ Nat.zero))
      := rfl
    _ = match Nat.succ (Nat.succ Nat.zero) with
        | Nat.zero => 3
        | Nat.succ k' => Nat.succ (plus 3 k')
      := rfl
    _ = Nat.succ (plus 3 (Nat.succ Nat.zero))
      := rfl
    _ = Nat.succ (match Nat.succ Nat.zero with
                  | Nat.zero => 3
                  | Nat.succ k' => Nat.succ (plus 3 k'))
      := rfl
    _ = Nat.succ (Nat.succ (plus 3 Nat.zero))
      := rfl
    _ = Nat.succ (Nat.succ 3)
      := rfl
    _ = 5
      := rfl

-- 『Theorem Proving in Lean 4』でやったやつ
theorem div_lemma (n : Nat) (k : Nat) : n ≥ k ∧ k > 0 → n - k < n :=
  fun (h : n ≥ k ∧ k > 0) =>
    show n - k < n from
      Nat.sub_lt -- 0 < n → 0 < k → n - k < n
        (show 0 < n from
          calc 0
            _ < k := h.right -- 0 < k
            _ ≤ n := h.left  -- k ≤ n
        )
        (show 0 < k from h.right)

def div (n : Nat) (k : Nat) : Nat :=
  if h : n ≥ k ∧ k > 0
  then (div (n - k) k) + 1
  else 0
decreasing_by
  simp
  apply div_lemma
  exact h

end Section05
