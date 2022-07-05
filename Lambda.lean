import Std

structure Name where
  (str : String)
  (subscript : Nat)

abbrev Ctx := List Name

def main : IO UInt32 := do
  IO.println "hello"
  IO.println "world"
  return 0

def getFresh (name : Name) (ctx : Ctx) : IO Name := do
  let mut sofar := name
  for x in ctx do
    if x.str = sofar.str ∧ x.subscript ≥ sofar.subscript then
      sofar := {sofar with subscript := x.subscript + 1}
  return sofar

abbrev PosIn (name : α) (ctx : List α) := {n // ctx.get n = name}

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
    
def dumbRename (f : Name → Name) (injective_f : ∀ x y, f x = f y → x = y) : Lambda ctx → Lambda (ctx.map f)
  | Var name pos => Var (f name) (ctx.PosIn_map pos)
  | App callee argument => App (dumbRename f injective_f callee) (dumbRename f injective_f argument)
  | Abs name body p => Abs (f name) (dumbRename f injective_f body) $
    by
    rw [List.mem_map_iff f (f name)]