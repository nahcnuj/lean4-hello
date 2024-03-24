namespace Chapter10

namespace Hidden

class Inhabited (a : Type u) where
  default : a
export Inhabited (default) -- 今の名前空間にInhabited.defaultをエクスポート

instance : Inhabited Nat  where default := 0
instance : Inhabited Bool where default := false
instance : Inhabited Unit where default := ()
instance : Inhabited Prop where default := False

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := ((default : a), (default : b))

instance {a : Type u} [Inhabited b] : Inhabited (a → b) where
  default := fun (_ : a) => (default : b)

-- 練習として、List 型や Sum 型などの他の型のデフォルトインスタンスを定義してみよう。
instance {a : Type u} : Inhabited (List a) where
  default := []

instance [Inhabited a] {b : Type u} : Inhabited (Sum a b) where
  default := Sum.inl (default : a)
instance {a : Type u} [Inhabited b] : Inhabited (Sum a b) where
  default := Sum.inr (default : b)

example : (default : Sum Nat Int) = Sum.inl 0 := rfl
example : (default : Sum Int Bool) = Sum.inr false := rfl

end Hidden

end Chapter10
