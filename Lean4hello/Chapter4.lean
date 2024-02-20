namespace Chapter4
open Classical

-- 1.
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (show (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) from
      fun (h : ∀ x, p x ∧ q x) =>
        And.intro
          (show ∀ x, p x from
            fun x => show p x from (h x).left)
          (show ∀ x, q x from
            fun x => show q x from (h x).right)
    )
    (show (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) from
      fun (h : (∀ x, p x) ∧ (∀ x, q x)) => show ∀ x, p x ∧ q x from
        fun x => ⟨show p x from h.left x, show q x from h.right x⟩
    )
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : ∀ x, p x → q x =>
    fun hp : ∀ x, p x =>
      fun x => show q x from
        (show p x → q x from h x)
        (show p x       from hp x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) => show ∀ x, p x ∨ q x from
    fun x => show p x ∨ q x from
      h.elim
        (show (∀ x, p x) → p x ∨ q x from
          fun hp => Or.inl (show p x from hp x))
        (show (∀ x, q x) → p x ∨ q x from
          fun hq => Or.inr (show q x from hq x))

-- 2.
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  fun (a : α) => Iff.intro
    (show (∀_ : α, r) → r from
      fun h : (x : α) → r => show r from h a)
    (show r → ∀_ : α, r from
      fun hr : r => show α → r from fun _ => hr)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (show (∀x, p x ∨ r) → (∀x, p x) ∨ r from
      fun h : ∀x, p x ∨ r => show (∀x, p x) ∨ r from
        byCases -- `r`かどうかで結論の型が違うので場合分け
          (fun hr : r => Or.inr hr)
          (fun hnr : ¬r => Or.inl (fun x => (h x).elim
            (show p x → p x from id)
            (show r → p x from fun hr => absurd hr hnr))))
    (show (∀x, p x) ∨ r → ∀x, p x ∨ r from
      fun h : (∀x, p x) ∨ r => fun x => show p x ∨ r from
        h.elim
          (show (∀x, p x) → p x ∨ r from fun hp => Or.inl (hp x))
          (show r → p x ∨ r from fun hr => Or.inr hr))
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (show (∀x, r → p x) → (r → ∀x, p x) from
      fun h : ∀x, r → p x => fun r => fun x => show p x from (h x) r)
    (show (r → ∀x, p x) → ∀x, r → p x from
      fun h : r → ∀x, p x => fun x => fun hr => show p x from h hr x)

-- 3.
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have ⟨
    (h1 : shaves barber barber → ¬shaves barber barber),
    (h2 : ¬shaves barber barber → shaves barber barber)⟩ := h barber
  byCases
    (fun (hp : shaves barber barber) => (h1 hp) hp)
    (fun (hn : ¬shaves barber barber) => hn (h2 hn))

-- 4.
def even (n : Nat) : Prop := ∃x, n = 2 * x

def prime (n : Nat) : Prop := n > 1 → ∀p, 1 < p ∧ p < n → (¬∃k, n = k * p)

def infinitely_many_primes : Prop := ∀n : Nat, ∃p : Nat, p > n ∧ prime p

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃k, n = 2 ^ 2 ^ k + 1

def infinitely_many_Fermat_primes : Prop := ∀n : Nat, ∃p : Nat, p > n ∧ Fermat_prime p

def goldbach_conjecture : Prop :=
  -- 5より大きい任意の自然数は
  ∀n : Nat, n > 5 →
    -- 3つの素数の和で表される
    ∃(p q r : Nat), prime p ∧ prime q ∧ prime r → n = p + q + r

def Goldbach's_weak_conjecture : Prop :=
  -- 5より大きい任意の奇数は
  ∀n : Nat, n > 5 ∧ ¬ even n →
    -- 3つの素数の和で表される
    ∃(p q r : Nat), prime p ∧ prime q ∧ prime r → n = p + q + r

def Fermat's_last_theorem : Prop :=
  -- 3以上の自然数nについて
  ∀n : Nat, n >= 3 →
    -- xⁿ + yⁿ = zⁿ となる自然数の組 (x, y, z) は存在しない
    ¬∃(x y z : Nat), x > 0 ∧ y > 0 ∧ z > 0 → x^n + y^n = z^n

-- 5.
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  fun ⟨_, hr⟩ => hr
example (a : α) : r → (∃ _ : α, r) :=
  fun (hr : r) => ⟨a, hr⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (show (∃x, p x ∧ r) → (∃x, p x) ∧ r from
      fun ⟨x, (h : p x ∧ r)⟩ => ⟨show ∃x, p x from ⟨x, h.left⟩, show r from h.right⟩)
    (show (∃x, p x) ∧ r → (∃x, p x ∧ r) from
      fun ⟨⟨x, hpx⟩, hr⟩ => ⟨x, show p x ∧ r from ⟨hpx, hr⟩⟩)
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (show (∃x, p x ∨ q x) → (∃x, p x) ∨ (∃x, q x) from
      fun ⟨x, h⟩ => h.elim
        (fun hpx => Or.inl ⟨x, hpx⟩)
        (fun hqx => Or.inr ⟨x, hqx⟩))
    (show (∃x, p x) ∨ (∃x, q x) → (∃x, p x ∨ q x) from
      fun h => h.elim
        (fun ⟨x, (hpx : p x)⟩ => ⟨x, Or.inl hpx⟩)
        (fun ⟨x, (hqx : q x)⟩ => ⟨x, Or.inr hqx⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (show (∀x, p x) → ¬(∃x, ¬ p x) from
      fun hp : (x : α) → p x => show (∃x, p x → False) → False from
        fun h : ∃x, p x → False => show False from
          h.elim
            fun a : α => fun hpa : p a → False => show False from hpa (hp a))
    (show ¬ (∃x, ¬ p x) → (∀x, p x) from
      fun h : (∃x, p x → False) → False => show (x : α) → p x from
        fun x => byContradiction
          fun hnpx : ¬p x => show False from h ⟨x, hnpx⟩)
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (show (∃x, p x) → ¬(∀x, ¬p x) from
      fun ⟨x, (hpx : p x)⟩ => show (∀x, ¬p x) → False from
        fun hnp : (x : α) → ¬p x => show False from
          (hnp x) hpx)
    (show ¬(∀x, ¬p x) → ∃x, p x from
      fun h : (∀x, p x → False) → False => show ∃x, p x from
        byContradiction (fun hn : (∃x, p x) → False => show False from
          h (fun x => fun hpx : p x => show False from hn (Exists.intro x hpx))))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (show (¬∃x, p x) → ∀x, ¬p x from
      fun h : (∃x, p x) → False => fun x => show p x → False from
        fun hpx : p x => show False from h (Exists.intro x hpx))
    (show (∀x, ¬p x) → ¬∃x, p x from
      fun hnp : ∀x, ¬p x => fun ⟨x, hpx⟩ => show False from absurd hpx (hnp x))
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (show (¬∀x, p x) → ∃x, ¬p x from
      fun h : (∀x, p x) → False => show ∃x, ¬p x from
        byContradiction fun hn : ¬∃x, ¬p x => show False from
          -- (¬∃x, ¬p x) → ∀x, p x
          have hp : ∀x, p x := fun x => show p x from
            byContradiction fun hnpx : ¬p x => show False from
              hn (Exists.intro x hnpx)
          h hp)
    (show (∃x, ¬p x) → ¬∀x, p x from
      fun ⟨a, (hnpa : ¬p a)⟩ => fun hp : ∀x, p x => show False from
        hnpa (hp a))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (show (∀x, p x → r) → (∃x, p x) → r from
      fun h : (x : α) → p x → r => fun ⟨a, hpa⟩ => show r from
        h a hpa)
    (show ((∃x, p x) → r) → ∀x, p x → r from
      fun h : ((∃x, p x) → r) => fun x => fun hpx : p x => show r from
        h (Exists.intro x hpx))
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (show (∃x, p x → r) → (∀x, p x) → r from
      fun ⟨t, (hptr : p t → r)⟩ => fun hp : (x : α) → p x => show r from
        hptr (hp t))
    (show ((∀x, p x) → r) → (∃x, p x → r) from
      fun h : (∀x, p x) → r => show ∃x, p x → r from
        byCases -- `∀x, p x`を仮定したい気持ち...?
          (fun hp : ∀x, p x => Exists.intro a (fun _ : p a => show r from h hp))
          (fun hnp : ¬∀x, p x => byContradiction fun hnex : ¬∃x, p x → r => show False from
            hnp (show (x : α) → p x from
              fun x => byContradiction fun hnpx : ¬p x => show False from
                hnex ⟨x, (fun hpx : p x => show r from absurd hpx hnpx)⟩)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (show (∃x, r → p x) → (r → ∃x, p x) from
      fun ⟨x, (hrpx : r → p x)⟩ => fun hr : r => show ∃x, p x from
        Exists.intro x (show p x from hrpx hr))
    (show (r → ∃x, p x) → (∃x, r → p x) from
      fun hrex : r → ∃x, p x => show ∃x, r → p x from
        byCases -- `∃x, p x`が欲しい
          (fun hex : ∃x, p x => have ⟨x, hpx⟩ := hex
            ⟨x, show r → p x from fun _ => hpx⟩)
          (fun hnex : ¬∃x, p x =>
            ⟨a, show r → p a from fun hr => absurd (hrex hr) hnex⟩))

end Chapter4
