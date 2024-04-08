def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

-- def third (xs : List α) : α := xs[2] -- Error: failed to prove index is valid

def third (xs : List α) (ok : xs.length > 2) : α := xs[2] -- xs[2]'ok

example : String := third woodlandCritters (by simp [List.length])
-- テキストには`(by simp)`って書いてあったが、`⊢ 2 < List.length woodlandCritters`のゴールが残った

def unsafeThird [Inhabited α] (xs : List α) : α := xs[2]! -- [2]がなかったらpanic!

example : Type := List Empty -- `α`がコンストラクタを持っていないと困る（値を作れなくて返せないから）

example : 2 + 3 = 5 := rfl -- by simp
example : 15 - 8 = 7 := rfl -- by simp
example : "Hello, ".append "world" = "Hello, world" := rfl -- by simp

example : 5 < 18 := Nat.lt_add_of_pos_right (Nat.zero_lt_succ 12)
-- `rfl`は反射律`x = x`なので不等式には使えない

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4] -- xs[4]'ok
