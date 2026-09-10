/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman, Anne Baanen, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public meta import Mathlib.LinearAlgebra.Matrix.Defs
public meta import Qq

/-!
# Matrix notation
This file defines `!![a, b; c, d]` notation for finite matrices. Matrix literals are represented
by nested `Array`s and constructed using `Matrix.ofArrays`.
The notation also supports empty matrices: `!![,,,] : Matrix (Fin 0) (Fin 3) α` and
`!![;;;] : Matrix (Fin 3) (Fin 0) α`.
-/

@[expose] public section

namespace Matrix

universe u uₘ uₙ

variable {α : Type u} {m n : ℕ} {m' : Type uₘ} {n' : Type uₙ}

section ToExpr

open Lean Qq

/-- Construct a quoted array literal from quoted elements. -/
private meta def mkArrayLiteralQ {u : Level} {α : Q(Type u)} (elems : Array Q($α)) :
    Q(Array $α) :=
  let elemsList : Q(List $α) :=
    elems.foldr (init := q(List.nil)) fun e acc => q(List.cons $e $acc)
  q(List.toArray $elemsList)

/-- `Matrix.mkLiteralQ !![a, b; c, d]` produces the term `q(!![$a, $b; $c, $d])`. -/
meta def mkLiteralQ {u : Level} {α : Q(Type u)} {m n : Nat}
    (elems : Matrix (Fin m) (Fin n) Q($α)) : Q(Matrix (Fin $m) (Fin $n) $α) :=
  let elems : Array (Array Q($α)) := (List.finRange m).toArray.map fun i =>
    (List.finRange n).toArray.map fun j => elems i j
  have elemsArray : Q(Array (Array $α)) := mkArrayLiteralQ (elems.map mkArrayLiteralQ)
  have hAm : Q(Array.size $elemsArray = $m) :=
    mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit m)
  have hAn : Q(∀ i : Fin $m, Array.size $elemsArray[i] = $n) :=
    .lam `j (binderInfo := .default) q(Fin $m) <| 
      mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit n)
  q(Matrix.ofArrays $elemsArray $hAm $hAn)

/-- Matrices can be reflected whenever their entries can. We insert a `Matrix.of` to prevent
immediate decay to a function. -/
protected meta instance toExpr [ToLevel.{u}] [ToLevel.{uₘ}] [ToLevel.{uₙ}]
    [Lean.ToExpr α] [Lean.ToExpr m'] [Lean.ToExpr n'] [Lean.ToExpr (m' → n' → α)] :
    Lean.ToExpr (Matrix m' n' α) :=
  have eα : Q(Type $(toLevel.{u})) := toTypeExpr α
  have em' : Q(Type $(toLevel.{uₘ})) := toTypeExpr m'
  have en' : Q(Type $(toLevel.{uₙ})) := toTypeExpr n'
  { toTypeExpr :=
    q(Matrix $eα $em' $en')
    toExpr := fun M =>
      have eM : Q($em' → $en' → $eα) := toExpr (show m' → n' → α from M)
      q(Matrix.of $eM) }

end ToExpr

section Parser

open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr

/-- Notation for m×n matrices, aka `Matrix (Fin m) (Fin n) α`.
For instance:
* `!![a, b, c; d, e, f]` is the matrix with two rows and three columns, of type
  `Matrix (Fin 2) (Fin 3) α`
* `!![a, b, c]` is a row vector of type `Matrix (Fin 1) (Fin 3) α` (see also `Matrix.row`).
* `!![a; b; c]` is a column vector of type `Matrix (Fin 3) (Fin 1) α` (see also `Matrix.col`).
This notation implements some special cases:
* `!![,,]`, with `n` `,`s, is a term of type `Matrix (Fin 0) (Fin n) α`
* `!![;;]`, with `m` `;`s, is a term of type `Matrix (Fin m) (Fin 0) α`
* `!![]` is the 0×0 matrix
Under the hood, `!![a, b, c; d, e, f]` is syntax for
`Matrix.ofArrays #[#[a, b, c], #[d, e, f]] rfl (fun _ => rfl)`.
-/
syntax (name := matrixNotation)
  "!![" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term

@[inherit_doc matrixNotation]
syntax (name := matrixNotationRx0) "!![" ";"+ "]" : term

@[inherit_doc matrixNotation]
syntax (name := matrixNotation0xC) "!![" ","* "]" : term

macro_rules
  | `(!![$[$[$rows],*];*]) => do
    let m := rows.size
    let n := if h : 0 < m then rows[0].size else 0
    for row in rows do
      unless row.size = n do
        Macro.throwErrorAt (mkNullNode row) s!"\
          Rows must be of equal length; this row has {row.size} items, \
          the previous rows have {n}"
    let elems ← rows.mapM fun (row : Array _) => `(#[$row,*])
    `(@Matrix.ofArrays _ $(quote m) $(quote n) #[$elems,*] rfl (fun _ => rfl))
  | `(!![$[;%$semicolons]*]) => do
    let emptyVecs ← semicolons.mapM fun _ => `(#[])
    `(@Matrix.ofArrays _ $(quote semicolons.size) 0 #[$emptyVecs,*] rfl (fun _ => rfl))
  | `(!![$[,%$commas]*]) =>
    `(@Matrix.ofArrays _ 0 $(quote commas.size) #[] rfl finZeroElim)

/-- Delaborate entries supplied in row-major ordering into the `!![]` notation. -/
private meta def delabArrayMatrixNotation (m n : Nat) (elems : Array (Array Term)) :
    DelabM Term := do
  unless elems.size = m do
    failure
  if m = 0 then
    let commas := Array.replicate n (mkAtom ",")
    return ← `(!![$[,%$commas]*])
  unless (List.finRange m).all fun i => elems[i]!.size = n do
    failure
  if n = 0 then
    let semicolons := Array.replicate m (mkAtom ";")
    `(!![$[;%$semicolons]*])
  else
    let rows : Array (Array Term) := (List.finRange m).toArray.map fun i =>
      (List.finRange n).toArray.map fun j => elems[i]![j]!
    `(!![$[$[$rows],*];*])

/-- Delaborator for the `!![]` notation. -/
@[app_delab Matrix.ofArrays]
meta def delabMatrixNotation : Delab := whenNotPPOption getPPExplicit <|
  whenPPOption getPPNotation <|
  withOverApp 5 do
    let (_, args) := (← getExpr).getAppFnArgs
    let #[_, em, en, _, _] := args | failure
    let some m ← withNatValue em (pure ∘ some) | failure
    let some n ← withNatValue en (pure ∘ some) | failure
    let rows ← delabArrayLiteral (delabArrayLiteral delab)
    delabArrayMatrixNotation m n rows

end Parser

/-- Use `!![...]` notation for displaying a `Fin`-indexed matrix, for example:
```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance repr [Repr α] : Repr (Matrix (Fin m) (Fin n) α) where
  reprPrec f _p :=
    (Std.Format.bracket "!![" · "]") <|
      (Std.Format.joinSep · (";" ++ Std.Format.line)) <|
        (List.finRange m).map fun i =>
          Std.Format.fill <|
            (Std.Format.joinSep · ("," ++ Std.Format.line)) <|
            (List.finRange n).map fun j => _root_.repr (f i j)

end Matrix
