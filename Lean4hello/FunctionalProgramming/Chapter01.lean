namespace FunctionalProgramming

/-
# Chapter 1: Getting to Know Lean
-/
namespace Chapter01

/-
## 1.1 Evaluating Expressions
-/
namespace Section01

section Exercise
example : 42 + 19 = 61 := rfl
example : String.append "A" (String.append "B" "C") = "ABC" := rfl
example : String.append (String.append "A" "B") "C" = "ABC" := rfl
example : (if 3 == 3 then 5 else 7 : Nat) = 5 := rfl
example : (if 3 == 4 then "equal" else "not equal" : String) = "not equal" := rfl
end Exercise

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

section Exercise
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
end Exercise

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

/-
## 1.6 Polymorphism（多態性、多相性）

本書でpolymorphismは型を引数に取るdatatypeやdefinitionを指す。
-/
namespace Section06

/--
`PPoint`は座標について特定の表現を要求しない点を表現する型
-/
structure PPoint (α : Type) : Type where
  x : α
  y : α
  deriving Repr

/--
`natOrigin`は座標が自然数型である点としての原点を表す。

`PPoint`の（型）引数`α`がここでは`Nat`になっている。
-/
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

/--
`replaceX`は第2引数の点のx座標を第3引数の値に置き換えた点を返す。
-/
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

example : (α : Type) → PPoint α   → α   → PPoint α   := replaceX
-- 第1引数`α`で、第2引数以降の引数の型に現れる`α`が置き換えられる。
example :              PPoint Nat → Nat → PPoint Nat := replaceX Nat

example :                           Nat → PPoint Nat := replaceX Nat natOrigin
example :                                 PPoint Nat := replaceX Nat natOrigin 5

example : replaceX Nat natOrigin 5 = { x := 5, y := 0 } := rfl

inductive Sign : Type where
  | pos
  | neg

def posOfNegThree (s : Sign)
  : match s with
    | Sign.pos => Nat
    | Sign.neg => Int
  := match s with
      | Sign.pos => ( 3 : Nat)
      | Sign.neg => (-3 : Int)

example : Nat := posOfNegThree Sign.pos
example : Int := posOfNegThree Sign.neg

example : posOfNegThree Sign.pos = ( 3 : Nat) := rfl
example : posOfNegThree Sign.neg = (-3 : Int) := rfl

def primesUnder10 : List Nat := [2, 3, 5, 7]

namespace Hidden
inductive List (α : Type) : Type where
  | nil  : List α
  | cons : α → List α → List α
end Hidden

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

example : primesUnder10 = explicitPrimesUnder10 := rfl

def length (α : Type) (xs : List α) : Nat :=
  match xs with
    | []      => Nat.zero
    | _ :: ys => Nat.succ (length α ys)

example : length Nat primesUnder10 = 4 := rfl

-- 引数を`()`の代わりに`{}`で囲むと省略可になる。
def replaceX' {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

example : replaceX' natOrigin 5 = { x := 5, y := 0 } := rfl

def length' {α : Type} (xs : List α) : Nat :=
  match xs with
    | []      => Nat.zero
    | _ :: ys => Nat.succ (length' ys)

example : length' primesUnder10 = 4 := rfl

-- 標準ライブラリの`List`は`length`関数を持つ。
example : primesUnder10.length = 4 := rfl

-- List Intに対してだけ動作するList.lengthが欲しければαにIntを指定する。
example : List Int → Nat := List.length (α := Int)

namespace Hidden
inductive Option (α : Type) : Type where
  | none
  | some (val : α)
end Hidden

example : Option Nat := Option.none
example : Option Nat := Option.some 42

example : Option (Option Nat) := Option.none
example : Option (Option Nat) := Option.some Option.none
example : Option (Option Nat) := Option.some (Option.some 360)

def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
    | []     => Option.none
    | y :: _ => Option.some y

example : primesUnder10.head? = Option.some 2 := rfl

-- `[]`や`Option.none`からは`α`を推論できないので明示してあげる必要がある。
example : [].head? (α := Int)   = Option.none := rfl
-- 型アノテーションでも良い。
example : ([] : List Int).head? = Option.none := rfl

namespace Hidden
structure Prod (α β : Type) : Type where
  fst : α
  snd : β
end Hidden

example (α β : Type) : (α × β) = Prod α β := rfl

def fives  : Prod String Int := { fst := "five", snd := 5 }
def fives' : String × Int    := ("five", 5)
example : fives = fives' := rfl

-- どちらの表記も右結合
def sevens  : String ×  Int × Nat  := ("VII",  7, 4 + 3 )
def sevens' : String × (Int × Nat) := ("VII", (7, 4 + 3))
example : sevens = sevens' := rfl

namespace Hidden
inductive Sum (α β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
end Hidden

-- `⊕`は`\oplus`か`\o+`で入力できる
def PetName : Type := String ⊕ String

-- `Sum.inl`を犬の名前に、`Sum.inr`を猫の名前に使う、というようなことができる。
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]
  -- 犬、猫、犬、犬、猫

/--
`countDogs`は犬か猫の名前のリストから、犬の名前の数を返す。
-/
def countDogs (pets : List PetName) : Nat :=
  match pets with
    | []                    => Nat.zero
    | Sum.inl _ :: morePets => Nat.succ (countDogs morePets) -- 犬（なので数える）
    | Sum.inr _ :: morePets => countDogs morePets            -- 猫（なので数えない）

example : countDogs animals = 3 := rfl

namespace Hidden
inductive Unit : Type where
  | unit : Unit
end Hidden

example : Unit.unit = () := rfl

inductive ArithExpr (ann : Type) : Type
  | nat  : ann → Nat → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

abbrev SourcePos := Nat
example : ArithExpr SourcePos := ArithExpr.nat 1 5 -- 1行目にある`5`、みたいな

example : ArithExpr Unit := ArithExpr.nat () 42 -- 上の`SourcePos`に当たるような情報がない、といえる

namespace Hidden
inductive Empty : Type
-- no constructor
end Hidden

example : Type := Sum Nat Empty -- 右`Sum.inr`は使えない
example : Sum Nat Empty := Sum.inl 42

/-
Sum type, Product type, Unit typeの名前について

`α`型が`n`個の異なる値からなり、`b`型が`k`個の異なる値からなるとき、
Sum type     `α ⊕ β`は---それらの和---`n + k`個の値、
Product type `α × β`は---それらの積---`n * k`個の値からなる。

`Unit`型はただ1つの値`()`からなる。

`Bool`型は`true`,`false`の2つの値からなるから、
`Bool × Unit`型は`2 * 1 = 2`個の値---`(true, ()), (false, ())`---からなる。
`Bool ⊕ Unit`型は`2 + 1 = 3`個の値---`Sum.inl true, Sum.inl true, Sum.inr ()`---からなる。
-/

example : Type 0 = Type := rfl

inductive MyType : Type 1 where
  | ctor : (α : Type) → α → MyType
-- `Type`型を引数に取る関数は1つ上のuniverse levelに属する。

-- 定義しようとしている型をコンストラクタの引数で使うようなことはできない。
/-
inductive MyType' where
  | ctor : (MyType' → Nat) → MyType'
--          ^^^^^^^
-/

section Exercise

def List.last? {α : Type} (xs : List α) : Option α :=
  match xs with
    | []      => Option.none
    | y :: [] => Option.some y
    | _ :: ys => List.last? ys

example : List.last? [] (α := Nat) = Option.none := rfl
example : List.last? (42 :: List.nil) = (42 : Nat) := rfl
example : List.last? [1, 2, 3] = (3 : Nat) := rfl

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
    | []      => Option.none
    | x :: xs =>
        match predicate x with
          | true  => Option.some x
          | false => List.findFirst? xs predicate

example : List.findFirst? []              (fun x : Nat => x == 3) = Option.none   := rfl
example : List.findFirst? [3]             (fun x : Nat => x == 3) = Option.some 3 := rfl
example : List.findFirst? [1, 2, 3, 4, 3] (fun x : Nat => x == 3) = Option.some 3 := rfl
example : List.findFirst? [1, 2, 1, 2, 1] (fun x : Nat => x == 3) = Option.none   := rfl

def Prod.swap {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

example : Prod.swap (3, -2) = (-2, 3) := rfl

inductive PetName' : Type where
  | dog : String → PetName'
  | cat : String → PetName'
example : PetName' := PetName'.dog "Foo"
example : PetName' := PetName'.cat "Bar"

def animals' : List PetName' :=
  [PetName'.dog "Spot", PetName'.cat "Tiger", PetName'.dog "Fifi", PetName'.dog "Rex", PetName'.cat "Floof"]

def countDogs' (pets : List PetName') : Nat :=
  match pets with
    | []                         => Nat.zero
    | PetName'.dog _ :: morePets => Nat.succ (countDogs' morePets) -- 犬（なので数える）
    | PetName'.cat _ :: morePets => countDogs' morePets            -- 猫（なので数えない）

example : countDogs' animals' = 3 := rfl

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
    | [],      _       => []
    | _,       []      => []
    | x :: xs, y :: ys => (x, y) :: zip xs ys

example : zip [] []                  = ([] : List (Nat × Int)) := rfl
example : zip [1, 2, 3] []           = ([] : List (Nat × Int)) := rfl
example : zip [] [-3, -2, -1]        = ([] : List (Nat × Int)) := rfl
example : zip [1, 2, 3] [-3, -2, -1] = [(1, -3), (2, -2), (3, -1)] := rfl
example : zip [1, 2, 3] [-3, -2]     = [(1, -3), (2, -2)] := rfl

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with
    | Nat.zero,   _       => []
    | _,          []      => []
    | Nat.succ k, x :: xs => x :: take k xs

example : take 3 ["bolete", "oyster"] = ["bolete", "oyster"] := rfl
example : take 1 ["bolete", "oyster"] = ["bolete"]           := rfl

def f {α β γ : Type} (x : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match (x.snd : β ⊕ γ) with
    | Sum.inl b => Sum.inl (x.fst, b)
    | Sum.inr c => Sum.inr (x.fst, c)

def g {α : Type} (x : Bool × α) : α ⊕ α :=
  match x.fst with
    | true  => Sum.inl x.snd
    | false => Sum.inr x.snd
end Exercise

end Section06
