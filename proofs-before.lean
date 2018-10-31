attribute [simp] function.comp

section intro

variables {a b c d e : Type}

def modus_ponens : a → (a → b) → b := sorry

def modus_tollens : (b → empty) → (a → b) → (a → empty) := sorry

def ex_falso_quodlibet : empty → a := sorry

def eagle : (a → d → c) → a → (b → e → d) → b → e → c := sorry

def batman : (((a → empty) → empty) → empty) → (a → empty) := sorry

end intro

--------------------------------------------------------------------------------

section fix

variable fix {a : Type} : (a → a) → a
-- For example in Haskell one can define it as
--   fix :: (a -> a) -> a
--   fix f = f (fix f)

def wtf : empty := sorry

end fix

--------------------------------------------------------------------------------

structure {u v} iso (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

namespace iso

def inv {α β} (i : iso α β) : iso β α := sorry

def comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ := sorry

end iso

--------------------------------------------------------------------------------

def fiber {α β} (f : α → β) (y : β) := Σ' x : α, f x = y

def iscontr (α : Type) := Σ' x : α, Π y : α, x = y

structure eqv (α β : Type) :=
(f : α → β) (h : Π y : β, iscontr (fiber f y))

--------------------------------------------------------------------------------

section balanced

def iter {α} (g : α → α) : ℕ → α → α
| 0 := id
| (n + 1) := iter n ∘ g

def diter {β : Type → Type 1} {γ : Type → Type} (g : Π {α}, β (γ α) → β α) : Π (n : ℕ) {α}, β (iter γ n α) → β α
| 0 α := id
| (n + 1) α := g ∘ diter n

-- Perfectly Balanced Tree
inductive F (g : Type → Type) : Type → Type 1
| F₀ : Π {α}, α → F α
| F₁ : Π {α}, F (g α) → F α

-- `F G` is a general balanced tree (arbitrary branching factor at each node)
inductive G (α : Type) : Type
| G₀ : α → G
| G₁ : α → G → G

-- `F G₂₃` is balanced 2-3-tree
inductive G₂₃ (α : Type) : Type
| G₂ : α → α → G₂₃
| G₃ : α → α → α → G₂₃

def S (g : Type → Type) (α : Type) := Σ n : ℕ, iter g n α

def from_s {g α} (x : S g α) : F g α :=
diter (@F.F₁ g) x.1 (F.F₀ g x.2)

def to_s {g α} (x : F g α) : S g α :=
F.rec (λ α a, ⟨nat.zero, a⟩) (λ α a ih, ⟨nat.succ ih.1, ih.2⟩) x

def to_s_from_s {g α} (x : S g α) : to_s (from_s x) = x :=
begin
  simp [to_s, from_s],
  induction x with n x,
  induction n with m ih generalizing α,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

def from_s_to_s {g α} (x : F g α) : from_s (to_s x) = x :=
begin
  simp [to_s, from_s],
  induction x with β x β x ih,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

def sf_iso {g α} : iso (S g α) (F g α) :=
⟨from_s, to_s, to_s_from_s, from_s_to_s⟩

end balanced
