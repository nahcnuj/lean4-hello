namespace Chapter3
variable (p q r : Prop)

def x : Prop := False

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
      Decidable.of_not_not (fun hnq : ¬q => show False from absurd hp (h hnq))
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

end Chapter3
