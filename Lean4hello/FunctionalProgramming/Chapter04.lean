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
