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

inductive Lambda : Ctx → Type
  | Var (name : Name) : {n // ctx.get n = name} → Lambda ctx
  | App (callee : Lambda ctx) (argument : Lambda ctx) : Lambda ctx
  | Abs (name : Name) (body : Lambda (name :: ctx)) : name ∉ ctx → Lambda ctx

