/-
# Chapter 4: Overloading and Type Classes
-/

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7 -- Error: failed to synthesize instance: OfNat Pos 7
def seven : Pos := Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.one))))))

-- def fourteen : Pos := seven + seven -- Error: failed to synthesize instance: HAdd Pos Pos ?m.226

def Pos.plus : Pos → Pos → Pos
  | Pos.one,    k => Pos.succ k
  | Pos.succ n, k => Pos.succ (Pos.plus n k)

/-
class Add (α : Type u) where
  add : α → α → α
-/

instance : Add Pos where
  add := Pos.plus

def fourteen : Pos := seven + seven

def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1

example :    seven.toNat =  7 := rfl
example : fourteen.toNat = 14 := rfl

instance : ToString Pos where
  toString n := toString n.toNat

example : s!"{seven}" = "7" := rfl
example : toString fourteen = "14" := rfl

def Pos.mul : Pos → Pos → Pos
  | Pos.one,    k => k
  | Pos.succ n, k => Pos.mul n k + k

instance : Mul Pos where
  mul := Pos.mul

def fourtyNine : Pos := seven * seven
example : fourtyNine.toNat = 49 := rfl

/-
class OfNat (α : Type u) (_ : Nat) where
  ofNat : α
-/

inductive LT3 where
  | zero
  | one
  | two
deriving Repr

instance : OfNat LT3 0 := { ofNat := LT3.zero }
instance : OfNat LT3 1 := { ofNat := LT3.one  }
instance : OfNat LT3 2 := { ofNat := LT3.two  }

example : (0 : LT3) = LT3.zero := rfl
example : (1 : LT3) = LT3.one  := rfl
example : (2 : LT3) = LT3.two  := rfl
-- example : LT3 := (3 : LT3) -- Error: failed to synthesize instance: OfNat LT3 3

-- `Nat.succ n`に対して（のみ）`OfNat Pos`を定義
-- `Nat.zero`(`0`)には定義しない
instance {n : Nat} : OfNat Pos (Nat.succ n) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0     => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

example : Pos := 8
-- example : Pos := 0 -- Error: failed to synthesize instance: OfNat Pos 0

namespace Exercise

structure Pos where
  succ ::    -- constructor
  pred : Nat -- a field

def Pos.add : Pos → Pos → Pos
  | Pos.succ n, k => Pos.succ (n + k.pred.succ)

instance: Add Pos where
  add := Pos.add

example : /- 1 -/(Pos.succ 0) + /- 1 -/(Pos.succ 0) = /- 2 -/(Pos.succ 1) := rfl
example : /- 2 -/(Pos.succ 1) + /- 2 -/(Pos.succ 1) = /- 4 -/(Pos.succ 3) := rfl

def Pos.mul : Pos → Pos → Pos
  | Pos.succ  Nat.zero,    k => k
  | Pos.succ (Nat.succ n), k => Pos.add (Pos.mul (Pos.succ n) k) k

instance : Mul Pos where
  mul := Pos.mul

example : /- 1 -/(Pos.succ 0) * /- 1 -/(Pos.succ 0) = /- 1 -/(Pos.succ 0) := rfl
example : /- 3 -/(Pos.succ 2) * /- 2 -/(Pos.succ 1) = /- 6 -/(Pos.succ 5) := rfl

def Pos.toNat : Pos → Nat
  | Pos.succ n => Nat.succ n

instance : ToString Pos where
  toString x := toString x.toNat

instance {n : Nat} : OfNat Pos (Nat.succ n) where
  ofNat := Pos.succ n

example : (1 : Pos).pred = 0 := rfl
example : (8 : Pos).pred = 7 := rfl

inductive Even : Type where
  | zero : Even
  | next : Even → Even

def Even.add : Even → Even → Even
  | Even.zero,   k => k
  | Even.next n, k => Even.next (Even.add n k)

instance : Add Even where
  add := Even.add

def Even.mul : Even → Even → Even
  | Even.zero,   _ => Even.zero
  | Even.next n, k => Even.add (Even.mul n k) k

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even → Nat
  | Even.zero   => 0
  | Even.next n => 2 + n.toNat

example : Even.zero.toNat = 0 := rfl
example : (Even.next Even.zero).toNat = 2 := rfl

instance : ToString Even where
  toString x := toString x.toNat

inductive HttpMethod where
  | Get
  | Head
  | Post

instance : ToString HttpMethod where
  toString method :=
    match method with
      | .Get  => "GET"
      | .Head => "HEAD"
      | .Post => "POST"

-- Response...?
structure HttpRequest (method : HttpMethod) where
  uri     : String
  version : String

instance {method : HttpMethod} : ToString (HttpRequest method) where
  toString req :=
    let ⟨uri, version⟩ := req
    s!"{method} {uri} {version}"

example : toString (HttpRequest.mk "/" "HTTP/1.1" : HttpRequest HttpMethod.Get) = "GET / HTTP/1.1" := rfl

-- use a type class...?
class Action (α : Type u) where
  print : α → IO Unit

instance : Action (HttpRequest HttpMethod.Get) where
  print req := IO.println (toString req)

instance : Action (HttpRequest HttpMethod.Post) where
  print req := IO.println (toString req)

instance : Action (HttpRequest HttpMethod.Head) where
  print req := IO.println (toString req)

def tests : List (IO Unit) :=
  [ Action.print (HttpRequest.mk "/" "HTTP/1.1"      : HttpRequest HttpMethod.Get),
    Action.print (HttpRequest.mk "/about" "HTTP/1.1" : HttpRequest HttpMethod.Head),
    Action.print (HttpRequest.mk "/posts" "HTTP/1.1" : HttpRequest HttpMethod.Post),
  ]
example : tests = [IO.println "GET / HTTP/1.1", IO.println "HEAD /about HTTP/1.1", IO.println "POST /posts HTTP/1.1"] := rfl

-- test harness...?
def runTests : IO Unit := do
  let rec run : List (IO Unit) → IO Unit
    | []            => pure ()
    | test :: tests => do
        test
        run tests
  run tests
#eval runTests

end Exercise

#check (IO.println) --  IO.println : ?m.18037 → IO Unit
#check @IO.println  -- @IO.println : {α : Type u_1} → [inst : ToString α] → α → IO Unit

example {α : Type u} [ToString α] : α → IO Unit := IO.println

/--
`List.sum`は、`+`（型クラス`Add`）と`0`（`OfNat α 0`）が定義されている型`α`のリストを受け取り、リストの値の総和を返す関数です。
-/
def List.sum {α : Type u} [Add α] [OfNat α 0] : List α → α
  | []      => (0 : α)
  | a :: as => a + List.sum as

def fourNats : List Nat := [1,2,3,4]
example : fourNats.sum = 10 := rfl

def fourPos : List Pos := [1,2,3,4]
-- example : fourPos.sum = 10 := rfl -- Error: failed to synthesize instance: OfNat Pos 0
-- `0 : Pos`が存在しないのでエラー！

structure PPoint (α : Type u) where
  x : α
  y : α
  deriving Repr

instance [Add α]: Add (PPoint α) where
  add p q := { x := p.x + q.x, y := p.y + q.y : PPoint α }

/-
@OfNat.ofNat : {α : Type u_1} → (x : Nat) → [self : OfNat α x] → α
                                ^^^^^^^^^
                                 explicit

class OfNat (α : Type u) (_ : Nat) where
  ofNat : α
         ^^^just α
-/

example : (OfNat.ofNat (2 : Nat) : Pos) = (2 : Pos) := rfl

namespace Exercise

instance : OfNat Even 0 where
  ofNat := Even.zero
example : Even := 0

instance {prev : Nat} [OfNat Even prev] : OfNat Even (prev + 2) where
  ofNat := Even.next (OfNat.ofNat prev)
example : Even := 2
example : Even := 4
example : Even := 6
example : Even := 8
example : Even := 128
example : Even := 254
-- example : Even := 256 -- Error: failed to synthesize instance: OfNat Even 256
-- 127回まで再帰してくれた

end Exercise

def addNatPos : Nat → Pos → Pos
  | Nat.zero,   p => p
  | Nat.succ n, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, Nat.zero   => p
  | p, Nat.succ n => Pos.succ (addPosNat p n)

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

example : (3 : Nat) + (5 : Pos) = (8 : Pos) := rfl
example : (3 : Pos) + (5 : Nat) = (8 : Pos) := rfl

class HPlus (α : Type u) (β : Type v) (γ : Type w) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos
instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
example : (HPlus.hPlus (3 : Nat) (5 : Pos)) = (8 : Pos) := rfl
example : (HPlus.hPlus (3 : Pos) (5 : Nat)) = (8 : Pos) := rfl

/-
#eval (HPlus.hPlus (3 : Nat) (5 : Pos))
-- Error: typeclass instance problem is stuck, it is often due to metavariables: HPlus Nat Pos ?m.22024
-/

class HPlus' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hPlus : α → β → γ
instance : HPlus' Nat Pos Pos where
  hPlus := addNatPos
instance : HPlus' Pos Nat Pos where
  hPlus := addPosNat

#eval (HPlus'.hPlus (3 : Nat) (5 : Pos)) -- 8 : Pos

instance [Add α] : HPlus' α α α where
  hPlus := Add.add

example : HPlus'.hPlus (3 : Nat) (5 : Nat) = (8 : Nat) := rfl

#check HPlus'.hPlus (3 : Nat) -- : ?m.22246 → ?m.22248

@[default_instance]
instance [Add α] : HPlus' α α α where
  hPlus := Add.add

#check HPlus'.hPlus (3 : Nat) -- : Nat → Nat
#check HPlus'.hPlus (5 : Pos) -- : Pos → Pos

namespace Exercise

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p k := { x := k * p.x, y := k * p.y : PPoint α }

#eval { x := 2.5, y := 3.7 : PPoint Float } * 2.0
-- { x := 5.000000, y := 7.400000 }

end Exercise

def northernTrees : Array String := #["sloe", "birch", "elm", "oak"]
-- #check northernTrees[5] -- Error: failed to prove index is valid
-- #eval northernTrees[5] -- Crashed!

structure NonEmptyList (α : Type u) : Type u where
  head : α
  tail : List α

def witchNumber4 : NonEmptyList String := {
  head := "HAL",
  tail := [
    "ROna",
    "HI-ME",
    "100Ka",
  ],
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  -- 0番目には要素が必ず存在する
  | { head := h, tail := _ }, Nat.zero => some h
  -- 1番目以降はtail次第
  | { head := _, tail := []      }, Nat.succ _ => none
  | { head := _, tail := x :: xs }, Nat.succ n => get? { head := x, tail := xs } n

def NonEmptyList.get'? : NonEmptyList α → Nat → Option α
  | xs, Nat.zero   => some xs.head
  | xs, Nat.succ n => xs.tail.get? n -- `List.get?`を使っている

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem witchNumber4HasZerothMember : witchNumber4.inBounds 0 :=
  show 0 ≤ witchNumber4.tail.length from
    Nat.zero_le witchNumber4.tail.length

example : witchNumber4.inBounds 1 :=
  show 1 ≤ witchNumber4.tail.length from
    calc 1
      _ ≤ 2                        := Nat.le_succ _
      _ ≤ 3                        := Nat.le_succ _
      _ = witchNumber4.tail.length := rfl

example : witchNumber4.inBounds 3 :=
  show 3 ≤ witchNumber4.tail.length from
    calc 3
      _ ≤ 3                        := Nat.le_of_eq rfl
      _ = witchNumber4.tail.length := rfl

example : ¬(witchNumber4.inBounds 4) :=
  show ¬(4 ≤ witchNumber4.tail.length) from
  show ¬(4 ≤ 3) from
    Nat.not_succ_le_self 3

def NonEmptyList.get : (xs : NonEmptyList α) → (i : Nat) → (xs.inBounds i) → α
  | xs, Nat.zero,   _  => xs.head
  | xs, Nat.succ n, ok => xs.tail[n]'ok
      -- xs.inBounds i は i ≤ xs.tail.length で Nat.succ n ≤ xs.tail.length つまり n < xs.tail.length だから要素は存在する

/-
GetElem.{u, v, w}
  (cont : Type u)                      -- リストの型
  (idx : Type v)                       -- インデックスの型
  (elem : outParam (Type w))           -- リストから得られる要素の型
  (dom : outParam (cont → idx → Prop)) -- リストxsにインデックスiの要素が存在するか否かを表す述語
  : Type (max (max u v) w)
-/
instance :
  GetElem
    (NonEmptyList α)      -- リストの型
    Nat                   -- インデックスの型
    α                     -- リストから得られる要素の型
    NonEmptyList.inBounds -- リストxsにインデックスiの要素が存在するか否かを表す述語
where
  getElem := NonEmptyList.get

-- outParamは与えなくても推論してくれるという目印。
#check GetElem.getElem witchNumber4 0 -- getElem witchNumber4 0 : NonEmptyList.inBounds witchNumber4 0 → String
-- メソッドに与えなくて済むわけではない。
example : GetElem.getElem witchNumber4 0 witchNumber4HasZerothMember = "HAL" := rfl

example : witchNumber4[0] = "HAL"   := rfl
example : witchNumber4[1] = "ROna"  := rfl
example : witchNumber4[2] = "HI-ME" := rfl
example : witchNumber4[3] = "100Ka" := rfl
/-
この書き方で証明がいらないのは
> `arr[i]`: proves the proof side goal by `get_elem_tactic`
ということなのだろう。
-/
example : witchNumber4[0]'(by get_elem_tactic) = "HAL" := rfl

--

-- #check witchNumber4[4] -- Error: failed to prove index is valid

instance : GetElem (List α) Pos α (fun xs i => i.toNat < xs.length) where
  getElem xs i (ok : i.toNat < xs.length) := xs[i.toNat]'ok

def wn4 : List String := witchNumber4.head :: witchNumber4.tail

example : wn4[(1 : Pos)] = "ROna"  := rfl
example : wn4[(2 : Pos)] = "HI-ME" := rfl
example : wn4[(3 : Pos)] = "100Ka" := rfl

/--
p : PPoint α に対してp[false] = x、p[true] = yを返す。
要素の存在性を表す述語は任意の b : Bool に対して真とすれば良い。
-/
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem p b _ := if b then p.y else p.x

example : { x := 3, y := 5 : PPoint Nat }[false] = 3 := rfl
example : { x := 3, y := 5 : PPoint Nat }[true]  = 5 := rfl
