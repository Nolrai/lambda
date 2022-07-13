import Std
import Lean
import Mathlib.Init.Algebra.Order
import Mathlib.Data.Nat.Basic

open Std

abbrev Name := String × Nat
abbrev Name.str (x : Name) := x.1
abbrev Name.subscript (x : Name) := x.2

abbrev Ctx := List Name

def main : IO UInt32 := do
  IO.println "hello"
  IO.println "world"
  return 0

def getFresh (name : Name) : Ctx → Name
  | [] => name
  | x :: xs => 
    if x.str = name.str
      then ⟨name.str, max (getFresh name xs).subscript (x.subscript + 1)⟩
      else getFresh name xs

-- the smallest number larger than every thing in the list
def List.max' : List Nat → Nat
  | [] => 0
  | x :: xs => _root_.max (x + 1) xs.max'

def getFreshSlow (name : Name) (ctx : Ctx) : Name :=
  ⟨name.str, max name.subscript (((ctx.filter (λ x => x.str = name.str)).map Name.subscript).max')⟩

theorem getFreshPreservesStr : ∀ ctx name, (getFresh name ctx).str = name.str
  | [], (str, _) => by simp [Name.str, getFresh]
  | (x_str, s_sub)::xs, (str, sub) =>
    by
    simp [Name.str, getFresh]
    by_cases x_str = str
    case pos =>
      rw [if_pos h]
    case neg =>
      rw [if_neg h]
      apply getFreshPreservesStr xs (str, sub)

theorem max_zero : ∀ (x : Nat), max x 0 = x
  | 0 => by 
    simp [max]
  | n + 1 => by
    simp [max]
    rw [if_pos]
    apply Nat.zero_lt_succ

theorem Nat.le_eq_lt_or_eq (x y : Nat) : (x ≤ y) = (x < y ∨ x = y) :=
  by
  apply propext
  apply Iff.intro
  case a.mp =>
    intro h
    induction h
    case refl => apply Or.inr rfl
    case step y h ih =>
      apply Or.inl
      cases ih
      case inl x_lt_y =>
        apply Nat.lt_trans x_lt_y
        apply Nat.lt_succ_self
      case inr x_eq_y =>
        cases x_eq_y
        apply Nat.lt_succ_self
  case a.mpr =>
    intro h
    cases h
    case inl h =>
      apply Nat.le_of_lt h
    case inr h =>
      rw [h]
      apply Nat.le_refl

theorem zero_max : ∀ (x : Nat), max 0 x = x
  | 0 => by 
    simp [max]
  | n + 1 => by
    simp [max]
    rw [if_neg]
    apply Nat.not_lt_zero (n + 1)

theorem succ_max_succ : ∀ x y : Nat, max (x + 1) (y + 1) = (max x y) + 1 :=
  fun x y =>
  if h : y < x
    then by
      simp [max]
      rw [if_pos (Nat.succ_lt_succ h), if_pos h]
    else by
      simp [max]
      rw [if_neg, if_neg h]
      intros h'
      apply h
      apply Nat.lt_of_succ_lt_succ h'

theorem lt_max_left (x y z : Nat) (lt_left : x < y) : x < max y z :=
  if h : z < y
    then by
      simp [max]
      rw [if_pos h]
      assumption
    else by
      simp [max]
      rw [if_neg h]
      apply Nat.lt_of_lt_of_le lt_left
      rw [← Nat.not_lt_eq]
      exact h
    
theorem lt_max_right (x y z : Nat) (lt_right : x < z) : x < max y z :=
  if h : z < y
    then by
      simp [max]
      rw [if_pos h]
      apply Nat.lt_trans lt_right h
    else by
      simp [max]
      rw [if_neg h]
      exact lt_right

#check max_assoc

theorem getFreshSpec : getFresh = getFreshSlow :=
  by
  funext name ctx
  cases name with 
  | mk str sub =>
  induction ctx
  case nil =>
    simp [getFresh, getFreshSlow, List.max', Name.subscript]
    rw [max_zero]
  case cons x xs ih =>
    cases x with | mk xstr xsub =>
    simp [getFresh, getFreshSlow, List.max', Name.subscript, Name.str]
    simp [List.max', List.map, List.filter]
    by_cases (xstr = str)
    case pos =>
      have pos := h; clear h
      simp [if_pos pos]
      rw [decide_eq_true pos]
      simp
      rw [ih]
      simp [getFresh, getFreshSlow, List.max', Name.subscript, Name.str]
      have : ∀ a b c : Nat, max (max a b) c = max a (max c b) := 
        by
        intros a b c
        rw [max_comm c b]
        apply Eq.symm
        rw [max_assoc]
      apply this
    case neg =>
      have neg := h; clear h
      simp [if_neg neg]
      rw [decide_eq_false neg]
      simp
      rw [ih]
      simp [getFresh, getFreshSlow, List.max', Name.subscript, Name.str]

theorem getFreshIsFresh_aux x : 
  ∀ (l : List Name) (y) (y_in : y ∈ l) (str_eq : y.str = x.str), 
    y.subscript < (getFresh x l).subscript :=
  λ l y y_in str_eq =>
    by
    cases y_in
    case head l =>
      simp [getFresh]
      rw [if_pos]
      simp [Name.subscript]
      apply lt_max_right
      apply Nat.lt_succ_of_le
      apply Nat.le_refl
      assumption
    case tail z zs y_in =>
      simp [getFresh]
      have str_eq : Decidable (z.str = x.str) := instDecidableEqString z.str x.str
      cases str_eq
      case isTrue xz =>
        rw [if_pos xz]
        simp [Name.subscript]
        apply lt_max_left
        apply getFreshIsFresh_aux
        apply y_in
        apply str_eq
      case isFalse xz =>
        rw [if_neg xz]
        apply getFreshIsFresh_aux
        apply y_in
        apply str_eq

theorem getFreshIsFresh x (zs : Ctx) y : y = getFresh x zs → y ∉ zs :=
  by
  intros y_eq y_in
  have str_eq : y.str = x.str := 
    by
    rw [y_eq]
    apply getFreshPreservesStr zs x
  have : y.subscript < (getFresh x zs).subscript := getFreshIsFresh_aux x zs y y_in str_eq
  rw [← y_eq] at this
  apply lt_irrefl y.subscript this

theorem List.get_map_aux (f : α → β) (a : α) : ∀ (n : Nat) (ctx : List α) (p : _), 
  ∃ q, (ctx.map f).get ⟨n, p⟩ = f (ctx.get ⟨n, q⟩)
  | n, [], p => (Nat.not_lt_zero _ p).elim
  | 0, x :: xs, p => ⟨Nat.zero_lt_succ _, rfl⟩
  | n +1, x :: xs, p => 
    by 
    constructor
    case w =>
      simp [map, length_map] at p
      exact p
    case h =>
      simp [get]
      have n_lt : n < length (map f xs) := Nat.lt_of_succ_lt_succ p
      have ⟨q', h'⟩ := get_map_aux f a n xs n_lt
      rw [h']

abbrev PosIn x (xs : List α) := {n // xs.get n = x}

def List.PosIn_map {name : α} {ctx : List α} {f : α → β} : PosIn name ctx → PosIn (f name) (ctx.map f)
  | {val := val, property := prop} =>
  have val_isLt : val.val < length (map f ctx) := by rw [length_map] exact val.isLt 
  {
      val := ⟨val.val, val_isLt⟩,
      property := by
        have ⟨q', h'⟩ := get_map_aux f name val ctx val_isLt
        cases val
        case mk val val_isLt' =>
        rw [h', prop]
  }

inductive Lambda : Ctx → Type
  | Var (name : Name) : {n // ctx.get n = name} → Lambda ctx
  | App (callee : Lambda ctx) (argument : Lambda ctx) : Lambda ctx
  | Abs (name : Name) (body : Lambda (name :: ctx)) : name ∉ ctx → Lambda ctx

open Lambda

theorem List.mem_map_iff (f : α → β) (a : β) (l : List α) : a ∈ l.map f ↔ ∃ b, b ∈ l ∧ a = f b :=
  by
  induction l
  case nil =>
    apply Iff.trans (_ : _ ↔ False)
    rw [Iff.comm, iff_false]
    intros hyp
    have ⟨b, b_in_nil, _⟩ := hyp
    cases b_in_nil
    simp [map]
    intros hyp
    cases hyp
  case cons x xs xs_ih =>
    simp [map]
    apply Iff.intro
    case mp =>
      intros h
      cases h
      case head =>
        exists x
        constructor
        case left => apply Mem.head
        case right => rfl
      case tail a_mem =>
        have : ∀ γ (z : γ) (zs : List γ), Mem z zs = (z ∈ zs) := fun γ z zs => rfl
        rw [this, xs_ih] at a_mem
        have ⟨b, b_mem, b_eq⟩ := a_mem
        exists b
        constructor
        apply Mem.tail
        apply b_mem
        apply b_eq
    case mpr =>
      intros h
      have ⟨b, b_mem, b_eq⟩ := h
      cases b_mem
      case head =>
        rw [b_eq]
        constructor
      case tail b_mem =>
        apply Mem.tail
        show a ∈ map f xs
        rw [xs_ih]
        exists b
        
def getDecidable (P : Prop) [Decidable P] : Decidable P :=
  if h : P
    then isTrue h
    else isFalse h

  

  