namespace Chapter8
section
open Nat

def natToBin : Nat → List Nat
  | 0   => [0]
  | 1   => [1]
  | n+2 =>
      -- 再帰後の項が元より「小さい」というためのヒント
      have : (n + 2) / 2 < n + 2 := -- sorry
        Nat.div_lt_self (n := n + 2) (k := 2)
          (show 0 < n + 2 from Nat.succ_pos (n + 1))
          (show 1 < 2     from Nat.succ_lt_succ (Nat.succ_pos 0))
      natToBin ((n + 2) / 2) ++ [n % 2]

/-
#eval natToBin 1234567
-- [1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1]
-/

example : natToBin 0 = [0] := rfl
example : natToBin 1 = [1] := rfl
example : natToBin 2 = [1, 0] := rfl
example : natToBin 4 = [1, 0, 0] := rfl
example : natToBin 8 = [1, 0, 0, 0] := rfl

/-
練習として
natToBin 2ⁿ = (10...0)₂ (n copies of 0's after 1)
を示してみる。

途中で必要になったので、
補題として
m ≥ 1 に対して `natToBin 2*m = natToBin m ++ [0]` を示す。
※整礎帰納法ではなく普通の帰納法。
-/
theorem natToBin_double (n : Nat) : natToBin ((n+1) * 2) = natToBin (n+1) ++ [0] :=
  Nat.recOn n
    (show natToBin (1 * 2) = natToBin 1 ++ [0] from rfl)
    (fun n _ => show natToBin ((n+2) * 2) = natToBin (n+2) ++ [0] from
      -- TODO 帰納法の仮定を使っていないのが気になる
      -- `(n+2) * 2`のままnatToBinを一回展開したほうが良いのかも？
      have aux (m : Nat) : 0 < 2 ∧ 2 ≤ (m+1) * 2 :=
        And.intro
          (show 0 < 2               from Nat.succ_pos _)
          (show 1 * 2 ≤ (m + 1) * 2 from Nat.mul_le_mul_right 2 (Nat.succ_le_of_lt (Nat.zero_lt_succ m)))
      calc natToBin ((n+2) * 2)
        _ = natToBin ((n+1) * 2 + 2)                          := congrArg _ (Nat.succ_mul ..)
        _ = natToBin (((n+1) * 2 + 2) / 2) ++ [(n+1) * 2 % 2] := by conv => lhs; unfold natToBin; simp
        _ = natToBin (n+2) ++ [(n+1) * 2 % 2] :=
              have : ((n+1) * 2 + 2) / 2 = n+2 :=
                calc ((n+1) * 2 + 2) / 2
                  _ = ((n+1) * 2 + 1 * 2) / 2 := rfl
                  _ = ((n+1) + 1) * 2 / 2 := congrArg (· / 2) (Nat.right_distrib ..).symm
                  _ = (n + 1 + 1) :=
                      have (m : Nat) : m * 2 / 2 = m :=
                        Nat.recOn m
                          (show 0 * 2 / 2 = 0 from rfl)
                          (fun m ih => show (m+1) * 2 / 2 = m+1 from
                            calc (m+1) * 2 / 2
                              _ = if 0 < 2 ∧ 2 ≤ (m + 1) * 2 then ((m + 1) * 2 - 2) / 2 + 1 else 0 := div_eq ..
                              _ = ((m + 1) * 2 - 2) / 2 + 1 := if_pos (aux m)
                              _ = (m * 2 + 2 - 2) / 2 + 1   := congrArg (fun n => (n - 2) / 2 + 1) (Nat.right_distrib m 1 2)
                              _ = (m * 2) / 2 + 1           := rfl
                              _ = m + 1                     := congrArg succ ih
                          )
                      this _
                  _ = n+2 := rfl
              congrArg (natToBin · ++ _) this
        _ = natToBin (n+2) ++ [0] :=
              congrArg (_ ++ [·]) (show (n+1) * 2 % 2 = 0 from
                have (m : Nat) : m * 2 % 2 = 0 :=
                  Nat.recOn m
                    (show 0 * 2 % 2 = 0 from rfl)
                    (fun m ih => show (m+1) * 2 % 2 = 0 from
                      calc (m+1) * 2 % 2
                        _ = if 0 < 2 ∧ 2 ≤ (m + 1) * 2 then ((m + 1) * 2 - 2) % 2 else (m + 1) * 2 := Nat.mod_eq ..
                        _ = ((m + 1) * 2 - 2) % 2 := if_pos (aux m)
                        _ = (m * 2 + 2 - 2) % 2   := congrArg (fun n => (n - 2) % 2) (Nat.right_distrib m 1 2)
                        _ = (m * 2) % 2           := rfl
                        _ = 0                     := ih
                    )
                this _
              )
    )

example (n : Nat) : natToBin (2 ^ n) = [1] ++ List.replicate n 0 :=
  Nat.recOn n
    (show natToBin (2 ^ 0) = [1] from
      calc  natToBin (2 ^ 0)
        _ = natToBin 1       := congrArg _ (Nat.pow_zero _)
     -- _ = [1]              := rfl
    )
    (fun n ih => show natToBin (2 ^ succ n) = [1] ++ List.replicate (succ n) 0 from
      have aux : 2^n - 1 + 1 = 2^n :=
        have : 1 ≤ 2^n := (Nat.succ_le_of_lt (Nat.pos_pow_of_pos n (Nat.succ_pos _)))
        Nat.sub_add_cancel this
      calc  natToBin (2 ^ succ n)
        _ = natToBin (2 ^ n * 2)               := congrArg _ (Nat.pow_succ ..)
        _ = natToBin ((2 ^ n - 1 + 1) * 2)     := congrArg (fun n => natToBin (n * 2)) aux.symm
        _ = natToBin (2 ^ n - 1 + 1) ++ [0]    := natToBin_double (2 ^ n - 1)
        _ = natToBin (2 ^ n) ++ [0]            := congrArg (natToBin · ++ [0]) aux
        _ = [1] ++ List.replicate n 0 ++ [0]   := congrArg (· ++ [0]) ih
        _ = [1] ++ (List.replicate n 0 ++ [0]) := List.append_assoc ..
        _ = [1] ++ (List.replicate (succ n) 0) :=
            have : List.replicate (succ n) 0 = List.replicate n 0 ++ [0] :=
              Nat.recOn n
                (show List.replicate 1 0 = List.replicate 0 0 ++ [0] from rfl)
                (fun n ih => show List.replicate (succ (succ n)) 0 = List.replicate (succ n) 0 ++ [0] from
                  calc List.replicate (succ (succ n)) 0
                 -- _ = 0 :: List.replicate (Nat.add (succ n) 0) 0 := rfl -- by conv => lhs; unfold List.replicate
                    _ = 0 :: List.replicate (succ n) 0             := rfl
                    _ = 0 :: (List.replicate n 0 ++ [0])           := congrArg _ ih
                    _ = 0 :: List.replicate n 0 ++ [0]             := (List.cons_append ..).symm
                    _ = List.replicate (succ n) 0 ++ [0]           := rfl
                )
            congrArg _ this.symm
    )
/-
#print List.replicate
-- `brecOn`使った定義から
-- `List.replicate (succ (succ n)) 0 = 0 :: List.replicate (succ n) 0`が`rfl`で成り立つのが分からなかった...
-/
end

/-
名前の衝突を避けるために名前空間 Hidden を開き、等式コンパイラを使って自然数上の加法、乗法、べき乗を定義せよ。
次に、等式コンパイラを使って、それらの基本的な性質を証明せよ。
-/
namespace Hidden

inductive Nat
  | zero : Nat
  | succ : Nat → Nat

namespace Nat

def add (n : Nat) : Nat → Nat
  | zero   => n
  | succ m => succ (add n m)

theorem add_zero : ∀ (n : Nat), add n zero = n
  | _ => rfl
theorem add_succ : ∀ (n m : Nat), add n (succ m) = succ (add n m)
  | _, _ => rfl

theorem succ_add : ∀ (n m : Nat), add (succ n) m = succ (add n m)
  | _, zero   => rfl
  | n, succ m => show add (succ n) (succ m) = succ (add n (succ m)) from
                 show succ (add (succ n) m) = succ (succ (add n m)) from
                   congrArg succ (succ_add n m)

theorem zero_add : ∀ (n : Nat), add zero n = n
  | zero   => rfl
  | succ n => show add zero (succ n) = succ n from
              show succ (add zero n) = succ n from
                congrArg succ (zero_add n)

theorem add_comm : ∀ (n m : Nat), add n m = add m n
  | zero,   zero   => rfl
  | succ n, zero   => show add (succ n) zero = add zero (succ n) from
                      show succ n = succ (add zero n) from
                        congrArg succ (zero_add n).symm
  | zero,   succ m => show add zero (succ m) = add (succ m) zero from
                      show succ (add zero m) = succ m from
                        congrArg succ (zero_add m)
  | succ n, succ m => show add (succ n) (succ m) = add (succ m) (succ n) from
                      show succ (add (succ n) m) = succ (add (succ m) n) from
                      --         succ (add n m)  =       add (succ m) n  -- succ_add n m
                        congrArg succ (add_comm n (succ m) ▸ (succ_add n m))
                      -- by simp [succ_add, add_comm]

theorem add_assoc : ∀ (n m k : Nat), add (add n m) k = add n (add m k)
  | _,      _,      zero   => by rfl
  | zero,   _,      succ k => by simp [zero_add]
  | succ n, zero,   succ k => by simp [add_zero, zero_add]
  | succ n, succ m, succ k => by simp [succ_add, add_assoc]

theorem add_left_comm : ∀ (n m k : Nat), add n (add m k) = add m (add n k)
  | _,      _,      zero   => by simp [add_zero, add_comm]
  | _,      zero,   succ k => by simp [zero_add]
  | zero,   succ m, succ k => by simp [zero_add]
  | succ n, succ m, succ k => by simp [succ_add, add_succ, add_left_comm]

def mul (n : Nat) : Nat → Nat
  | zero   => zero
  | succ m => add (mul n m) n

theorem mul_zero : ∀ (n : Nat), mul n zero = zero
  | _ => rfl
theorem mul_succ : ∀ (n m : Nat), mul n (succ m) = add (mul n m) n
  | _, _ => rfl

theorem zero_mul : ∀ (m : Nat), mul zero m = zero
  | zero   => by rfl
  | succ m => by simp [mul_succ, add_zero, zero_mul]
theorem succ_mul : ∀ (n m : Nat), mul (succ n) m = add (mul n m) m
  | _,      zero   => by rfl
  | zero,   succ m => by simp [mul_succ, add_succ, add_zero, succ_mul]
  | succ n, succ m => by simp [mul_succ, add_succ, succ_mul, succ_add, add_assoc, add_comm n m]

theorem mul_comm : ∀ (n m : Nat), mul n m = mul m n
  | zero,   zero   => by rfl
  | succ n, zero   => by simp [mul_zero, zero_mul]
  | zero,   succ m => by simp [mul_zero, zero_mul]
  | succ n, succ m => by simp [mul_succ, add_succ, succ_mul, add_assoc, add_comm n m, mul_comm n m]

theorem right_distrib : ∀ (n m k : Nat), mul (add n m) k = add (mul n k) (mul m k)
  | _,      _,      zero   => by rfl
  | _,      zero,   succ k => by simp [add_zero, zero_mul]
  | zero,   succ m, succ k => by simp [zero_add, zero_mul]
  | succ n, succ m, succ k => by simp [mul_succ, add_succ, succ_add, succ_mul, right_distrib, add_assoc, add_left_comm]

theorem left_distrib : ∀ (n m k : Nat), mul n (add m k) = add (mul n m) (mul n k)
  | _,      _,      zero   => by rfl
  | _,      zero,   succ k => by simp [zero_add, mul_zero]
  | zero,   succ m, succ k => by simp [zero_mul, zero_add]
  | succ n, succ m, succ k => by simp [succ_mul, mul_succ, add_succ, succ_add, left_distrib, add_assoc, add_left_comm]

theorem mul_assoc : ∀ (n m k : Nat), mul (mul n m) k = mul n (mul m k)
  | n, m, zero   => by rfl
  | n, m, succ k => by simp [mul_succ, mul_assoc, left_distrib]
-- Nat.mul_assocの証明をカンニングしてしまった

theorem mul_left_comm : ∀ (n m k : Nat), mul n (mul m k) = mul m (mul n k)
  | n, m, zero   => by rfl
  | n, m, succ k => by simp [mul_succ, left_distrib, mul_left_comm, mul_comm]

def pow (n : Nat) : Nat → Nat
  | zero   => succ zero
  | succ m => mul n (pow n m)

theorem pow_zero : ∀ (n : Nat), pow n zero = succ zero
  | _ => rfl

theorem pow_succ : ∀ (n m : Nat), pow n (succ m) = mul n (pow n m)
  | _, _ => rfl

/--
指数法則 xⁿ × xᵐ = xⁿ⁺ᵐ
-/
theorem pow_mul_pow : ∀ (x n m : Nat), mul (pow x n) (pow x m) = pow x (add n m)
  | x, n, zero   => by simp [pow_zero, mul_succ, mul_zero, zero_add, add_zero]
  | x, n, succ m => by simp [pow_succ, mul_left_comm, pow_mul_pow, add_succ]

end Nat

/-
同様に、等式コンパイラを使ってリストに対する基本的な操作(reverse 関数など)を定義し、
リストに関する定理を帰納法で証明せよ。
-/

inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List

def append : List α → List α → List α
  | nil,       bs => bs
  | cons a as, bs => cons a (append as bs)

theorem append_nil : ∀ (as : List α), append as nil = as
  | nil       => by rfl
  | cons a as => by simp [append, append_nil]
theorem append_cons : ∀ (as : List α) (b : α) (bs : List α), append as (cons b bs) = append as (append (cons b nil) bs)
  | nil,       b, bs => by rfl
  | cons a as, b, bs => by simp [append]

theorem nil_append : ∀ (bs : List α), append nil bs = bs
  | _ => by rfl
theorem cons_append : ∀ (a : α) (as bs : List α), append (cons a as) bs = cons a (append as bs)
  | _ => by simp [append]

theorem append_assoc : ∀ (as bs cs : List α), append (append as bs) cs = append as (append bs cs)
  | nil,       bs, cs => by rfl
  | cons a as, bs, cs => by simp [cons_append, append_assoc]

def reverse : List α → List α
  | nil       => nil
  | cons a as => append (reverse as) (cons a nil)

theorem reverse_nil : reverse (nil : List α) = nil := rfl
theorem reverse_cons : ∀ (a : α) (as : List α), reverse (cons a as) = append (reverse as) (cons a nil)
  | a, as => by rfl

theorem reverse_append : ∀ (as bs : List α), reverse (append as bs) = append (reverse bs) (reverse as)
  | nil,       bs => by simp [reverse_nil, append_nil, nil_append]
  | cons a as, bs => by simp [cons_append, reverse_cons, reverse_append, append_assoc]

theorem reverse_reverse : ∀ (as : List α), reverse (reverse as) = as
  | nil       => by rfl
  | cons a as => by simp [reverse, append_cons, reverse_append, reverse_reverse, append]

end List

namespace Nat

/-
累積再帰を実行する自然数上の関数を自分で定義せよ。
-/
-- Tribonacci numbers
def trib : Nat → Nat
  | zero                 => succ zero
  | succ zero            => succ zero
  | succ (succ zero)     => succ (succ zero)
  | succ (succ (succ n)) => add (add (trib (succ (succ n))) (trib (succ n))) (trib n)

end Nat

/--
WellFounded.fix を自分で定義する方法を見つけられるか試してみよ。

```
#check WellFounded.fix
WellFounded.fix.{u, v} {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (hwf : WellFounded r)
  (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) : C x
```
-/
-- Sort v を Prop に限ればなんとか...
def wf_fix {α : Sort u} {C : α → Prop} {r : α → α → Prop} : WellFounded r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x :=
  fun hwf F x => Acc.brecOn (hwf.apply x) (fun (a : α) _ _ => hwf.induction a F) -- hwf.inductionのCがα → Propだ...

theorem wf_fix_eq {α : Sort u} {C : α → Prop} {r : α → α → Prop}
  (hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)
  : wf_fix hwf F = WellFounded.fix hwf F := rfl

/-
#check Acc.brecOn
Acc.brecOn.{u}
  {α : Sort u}
  {r : α → α → Prop}
  {motive✝ : (a : α) → Acc r a → Prop}
  {a✝ : α}
  (x✝ : Acc r a✝)
  (ih✝ : ∀ (a : α) (x : Acc r a), Acc.below x → motive✝ a x) : motive✝ a✝ x✝

そもそもAcc.brecOnのmotiveがPropだった...
-/

-- カンニングした：
noncomputable def wf_fix' {α : Sort u} {C : α → Sort v} {r : α → α → Prop} : WellFounded r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x :=
  fun hwf F x => Acc.ndrecOn (hwf.apply x) (fun a _ ih => F a ih)
  -- by induction (hwf.apply x) with
  --  | intro a _ ih => exact F a ih

-- 構造再帰のところでbrecOnしか紹介してなかっただろ！

/-
#check Acc.ndrecOn
Acc.ndrecOn.{u1, u2}
  {α : Sort u2}
  {r : α → α → Prop}
  {C : α → Sort u1}
  {a : α}
  (n : Acc r a)
  (m : (x : α) → (∀ (y : α), r y x → Acc r y) → ((y : α) → r y x → C y) → C x) : C a
-/

/-
節Dependent Pattern Matching (依存パターンマッチング)の例に従って、
2つのベクトル va vb を受け取り、va の末尾に vb を追加したベクトルを返す関数を定義せよ。
これは厄介で、補助関数を定義しなければならないだろう。
-/
section
open Nat
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α zero
  | cons : α → {n : Nat} → Vector α n → Vector α (succ n)

namespace Vector

def append {n m : Nat} : Vector α n → Vector α m → Vector α (add n m)
  | nil,       bs => zero_add _ ▸ bs
  | cons a as, bs => succ_add _ _ ▸ cons a (append as bs)
/-
bs : Vector α m から Vector α (add zero m) を得るには、
zero_add m : m = add zero m を使えば
zero_add m ▸ bs : Vector α (add zero m) となる。

v : Vector α (succ (add n m)) から Vector α (add (succ n) m) を得るには、
succ_add n m : add (succ n) m = succ (add n m) を使えば
succ_add n m ▸ v : Vector α (add (succ n) m) となる。
`▸`はEq.symmを勝手に使ってくれる。
-/

example : append (nil : Vector α zero) nil = nil := rfl
example : append (cons zero nil) nil = cons zero nil := rfl
example : append (cons zero nil) (cons (succ zero) nil) = cons zero (cons (succ zero) nil) := rfl
example : append (cons zero (cons zero (cons zero (cons zero nil)))) (cons (succ zero) nil) = cons zero (cons zero (cons zero (cons zero (cons (succ zero) nil)))) := rfl

/-
`h ▸ e` は `h : a = b` から `e : ... a` を `e : ... b` に変えてくれるけど、
置き換えるところが最後の引数ではないような場合、例えば、
`e : Vector a n` を `e : Vector b n` に変えるのはどうすれば良いだろう？

そもそも、nのない形で`Vector a`→`Vector b`とすれば良いのか。
-/
example {α β : Type u} : α = β → Vector α = Vector β :=
  fun (h : α = β) => h ▸ rfl
-- できた。

end Vector
end

end Hidden

section
open Nat

/-
次のような算術式の型を考える。
ここで、var n は変数 vₙを、const n は値が n である定数を表す。
各 var n を v n に評価した上で、このような式(Expr の項)を評価する関数を書け。
-/
inductive Expr where
  | const : Nat → Expr
  | var   : Nat → Expr
  | plus  : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr := -- (v₀ * 7) + (2 * v₁)
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

example : eval sampleVal sampleExpr = 47 := rfl

/-
補助関数 simpConst を使って、5 + 7 のような部分項を 12 に単純化する「定数融合関数」fuse を実装せよ。
plus や times を単純化するために、まず引数を再帰的に単純化せよ。
-/

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | plus e₁ e₂  => plus (simpConst e₁) (simpConst e₂)
  | times e₁ e₂ => times (simpConst e₁) (simpConst e₂)
  | e           => e

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e
  | plus (const _) (const _)    => rfl
  | plus (const _) (var _)      => rfl
  | plus (const _) (plus _ _)   => rfl
  | plus (const _) (times _ _)  => rfl
  | plus (var _)     _          => rfl
  | plus (plus _ _)  _          => rfl
  | plus (times _ _) _          => rfl
  | times (const _) (const _)   => rfl
  | times (const _) (var _)     => rfl
  | times (const _) (plus _ _)  => rfl
  | times (const _) (times _ _) => rfl
  | times (var _)     _         => rfl
  | times (plus _ _)  _         => rfl
  | times (times _ _) _         => rfl
  | const _                     => rfl
  | var _                       => rfl
-- 全部`rfl`で証明できたが、良い感じにwildcardにはなってくれないものか。。
-- defと同じように`| e => rfl`とでも書きたい…。

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e
  | const n     => rfl
  | var n       => rfl
  | plus e₁ e₂  => by simp [fuse, eval, simpConst_eq]
  | times e₁ e₂ => by simp [fuse, eval, simpConst_eq]
