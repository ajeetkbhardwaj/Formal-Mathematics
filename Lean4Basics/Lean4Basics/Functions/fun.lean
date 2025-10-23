import Mathlib.Tactic
import Mathlib.Data.Nat.Basic


open Classical

/- Injectivity -/
def is_injective {X Y : Type*} (f : X → Y) :=
  ∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂

/- Surjectivity -/
def is_surjective {X Y : Type*} (f : X → Y) :=
  ∀ y : Y, ∃ x : X, f x = y

/- Bijectivity -/
def is_bijective {X Y : Type*} (f : X → Y) :=
  is_injective f ∧ is_surjective f

/-
Bijective => Injective
-/
lemma bij_inj {X Y : Type*} {f : X → Y}
  (hf : is_bijective f) : is_injective f :=
by exact hf.left



/-
Bijective => Surjective
-/
lemma bij_surj {X Y : Type*} {f : X → Y}
  (hf : is_bijective f) : is_surjective f :=
by exact hf.right


/-
Surjective + Injective =>  Bijective
-/
lemma surj_inj_bij {X Y : Type*} {f : X → Y}
  (h_surj : is_surjective f) (h_inj : is_injective f) :
  is_bijective f :=
by exact ⟨h_inj, h_surj⟩

/-
1. Prove that If gof is injective then f is injective.
-/
lemma inj_comp_injfirst {X Y Z : Type*}
  {f : X → Y} {g : Y → Z}
  (h : is_injective (g ∘ f)) :
  is_injective f :=
by
  intro x₁ x₂ hfx
  apply h
  simp [hfx]

/-
2. Prove that if gof is surjective then g is surjective
-/
lemma surj_comp_surjsecond {X Y Z : Type*}
  {f : X → Y} {g : Y → Z}
  (h : is_surjective (g ∘ f)) :
  is_surjective g :=
by
  intro z
  obtain ⟨x, hx⟩ := h z
  use f x
  simpa using hx


/-
3. Prove that if fof is bijective then f is bijective
-/
lemma square_bij_bij {X : Type*} {f : X → X}
  (hff : is_bijective (f ∘ f)) :
  is_bijective f :=
by
  have hinj : is_injective f :=
    inj_comp_injfirst (bij_inj hff)
  have hsurj : is_surjective f :=
    surj_comp_surjsecond (bij_surj hff)
  exact ⟨hinj, hsurj⟩

/-
Examples of Maps
1. Neither Injective nor Surjective
2. Non Injective
3. Non Surjective
4. Bijective
-/

inductive A : Type
  | A₁ | A₂ | A₃
deriving DecidableEq, Repr

open A

def f : A → A
  | A₁ => A₁
  | A₂ => A₁
  | A₃ => A₂

lemma not_inj_f : ¬ is_injective f :=
by
  unfold is_injective
  push_neg
  use A₁, A₂
  simp [f]

lemma not_surj_f : ¬ is_surjective f :=
by
  unfold is_surjective
  push_neg
  use A₃
  intro x
  cases x <;> simp [f]

inductive B : Type
  | B₁ | B₂
deriving DecidableEq, Repr

open B

def g : B → B
  | B₁ => B₂
  | B₂ => B₁

/-
1. Prove that function g in example 4 is a bijective function
-/
lemma bij_g : is_bijective g := by
  -- injective
  have hinj : is_injective g := by
    intro x₁ x₂ h
    cases x₁
    case B₁ =>
      cases x₂
      case B₁ => rfl
      case B₂ => simp [g] at h; --contradiction
    case B₂ =>
      cases x₂
      case B₁ => simp [g] at h; --contradiction
      case B₂ => rfl
  -- surjective
  have hsurj : is_surjective g := by
    intro y
    cases y
    case B₁ => use B₂; simp [g]
    case B₂ => use B₁; simp [g]
  exact ⟨hinj, hsurj⟩
