
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

theorem eq1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
    apply Iff.intro
    · intro h1
      intro x
      intro h2
      apply h1
      exact ⟨x, h2⟩

    · intro h1
      intro h2
      obtain ⟨x1, h3⟩ := h2
      specialize h1 x1
      -- contradiction
      apply h1
      exact h3

theorem eq2 : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
  by
    apply Iff.intro
    · intro h x r
      exact h r x

    · intro h r x
      specialize h x
      exact h r

theorem eq3 : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) :=
  by
    apply Iff.intro
    · intro h
      obtain ⟨hr, hex⟩ := h
      rcases hex with ⟨x, hpx⟩
      exact ⟨x, hr, hpx⟩

    · intro h
      rcases h with ⟨x, hr, hpx⟩
      constructor
      exact hr
      exists x

theorem eq4 : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  by
    intro h x
    cases h with
    | inl hr =>
      left
      exact hr
    | inr hpx =>
      right
      specialize hpx x
      assumption

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical
#check Classical.byContradiction
#check Classical.em

theorem eq5 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
 by
    apply Iff.intro
    · intro h1
      apply Classical.byContradiction
      intro h2
      apply h1
      intro x
      apply Classical.byContradiction
      intro h3
      apply h2
      exact ⟨ x, h3 ⟩

    · intro h1 h2
      let ⟨x, npx⟩ := h1
      apply npx (h2 x)

theorem eq6 : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  by
    apply Iff.intro
    · intro h x
      cases h with
      | inl hr =>
        left
        assumption
      | inr h' =>
        right
        specialize h' x
        assumption
    · intro h
      have h1 := Classical.em r
      cases h1 with
      | inl hr =>
        left
        assumption
      | inr hnr =>
        right
        intro x
        specialize h x
        cases h with
        | inl hrr => contradiction
        | inr hpx =>
          exact hpx
