import CoreGeisha.Syntax
import CoreGeisha.Semantics

/-!
# Core Geisha: Proven Executable Small-Step Evaluator (`geisha-check --eval`)

Provides a fuel-bounded deterministic small-step evaluator `runSteps` for
sequential Core Geisha programs together with a machine-checked soundness
theorem (`runSteps_sound`, zero `sorry`) proving every evaluation result is a
true `Steps` execution trace of `CoreGeisha.Semantics`.

Used by `geisha-check --eval <fn> <file.gscore>` for differential conformance
testing between the Lean 4 formal semantics and `src/codegen.gsa` native binaries.
-/

namespace CoreGeisha

mutual
/-- Executable boolean decision procedure for `IsValue`. -/
def isValB : Expr → Bool
  | .lit _ => true
  | .loc _ => true
  | .taskRef _ => true
  | .syncRef _ _ => true
  | .lam _ _ _ _ => true
  | .tuple es => isValListB es
  | .makeData _ _ es => isValListB es
  | _ => false
termination_by e => sizeOf e

def isValListB : List Expr → Bool
  | [] => true
  | e :: es => isValB e && isValListB es
termination_by es => sizeOf es
end

mutual
theorem isValB_sound {e : Expr} (h : isValB e = true) : IsValue e := by
  cases e <;> simp only [isValB] at h <;> try cases h
  · exact .lit _
  · exact .loc _
  · exact .taskRef _
  · exact .syncRef _ _
  · exact .tuple (isValListB_sound h)
  · exact .lam _ _ _ _
  · exact .makeData _ _ (isValListB_sound h)
termination_by sizeOf e

theorem isValListB_sound {es : List Expr} (h : isValListB es = true) :
    ∀ x ∈ es, IsValue x := by
  cases es with
  | nil => intro _ hm; cases hm
  | cons a rest =>
    simp only [isValListB, Bool.and_eq_true] at h
    intro x hm
    rcases List.mem_cons.mp hm with heq | hr
    · rw [heq]; exact isValB_sound h.1
    · exact isValListB_sound h.2 x hr
termination_by sizeOf es
end

private def asTrap? : Expr → Option Trap
  | .trap t => some t
  | _ => none

private theorem asTrap?_sound {e : Expr} {t : Trap} (h : asTrap? e = some t) :
    e = .trap t := by
  cases e <;> simp [asTrap?] at h
  subst h; rfl

private def asBoolLit? : Expr → Option Bool
  | .lit (.bool b) => some b
  | _ => none

private theorem asBoolLit?_sound {e : Expr} {b : Bool} (h : asBoolLit? e = some b) :
    e = .lit (.bool b) := by
  cases e <;> simp [asBoolLit?] at h
  rename_i l
  cases l <;> simp at h
  subst h; rfl

private def asLit? : Expr → Option Lit
  | .lit l => some l
  | _ => none

private theorem asLit?_sound {e : Expr} {l : Lit} (h : asLit? e = some l) :
    e = .lit l := by
  cases e <;> simp [asLit?] at h
  subst h; rfl

private def asLam? : Expr → Option (Mode × List (Ident × Ty) × Ty × Expr)
  | .lam m ps ret body => some (m, ps, ret, body)
  | _ => none

private theorem asLam?_sound {e : Expr} {m : Mode} {ps : List (Ident × Ty)} {ret : Ty} {body : Expr}
    (h : asLam? e = some (m, ps, ret, body)) :
    e = .lam m ps ret body := by
  cases e <;> simp [asLam?] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl

private def asLoc? : Expr → Option Loc
  | .loc l => some l
  | _ => none

private theorem asLoc?_sound {e : Expr} {l : Loc} (h : asLoc? e = some l) :
    e = .loc l := by
  cases e <;> simp [asLoc?] at h
  subst h; rfl

private def asMakeData? : Expr → Option (Ident × Nat × List Expr)
  | .makeData adt tag vs => some (adt, tag, vs)
  | _ => none

private theorem asMakeData?_sound {e : Expr} {adt : Ident} {tag : Nat} {vs : List Expr}
    (h : asMakeData? e = some (adt, tag, vs)) :
    e = .makeData adt tag vs := by
  cases e <;> simp [asMakeData?] at h
  rcases h with ⟨rfl, rfl, rfl⟩; rfl

/-- Executable leftmost-trap finder after evaluated prefix values (`ListFirstTrap`). -/
def firstTrap? : List Expr → Option Trap
  | [] => none
  | e :: rest =>
    match asTrap? e with
    | some t => some t
    | none => if isValB e then firstTrap? rest else none

theorem firstTrap?_sound {es : List Expr} {t : Trap} (h : firstTrap? es = some t) :
    ListFirstTrap es t := by
  induction es with
  | nil => simp [firstTrap?] at h
  | cons e rest ih =>
    simp only [firstTrap?] at h
    cases ht : asTrap? e with
    | some tr =>
      rw [ht] at h; injection h with h; subst h
      rw [asTrap?_sound ht]
      exact .head _ _
    | none =>
      rw [ht] at h; dsimp only at h
      split at h
      · rename_i hv
        exact .tail (isValB_sound hv) (ih h)
      · cases h

mutual
/-- Deterministic single-step sequential reducer conforming to `Step Δ Φ emptyPool`. -/
def stepOnce (Δ : AdtEnv) (Φ : FunEnv) : Expr → Store → Option (Expr × Store)
  | .tuple es, σ =>
    match firstTrap? es with
    | some t => some (.trap t, σ)
    | none =>
      match stepListOnce Δ Φ es σ with
      | some (es', σ') => some (.tuple es', σ')
      | none => none
  | .block es, σ =>
    match es with
    | [] => some (.lit .unit, σ)
    | [e1] => some (e1, σ)
    | e1 :: e2 :: rest =>
      match asTrap? e1 with
      | some t => some (.trap t, σ)
      | none =>
        if isValB e1 then
          some (.block (e2 :: rest), σ)
        else
          match stepOnce Δ Φ e1 σ with
          | some (e1', σ') => some (.block (e1' :: e2 :: rest), σ')
          | none => none
  | .apply fn args, σ =>
    match asTrap? fn with
    | some t => some (.trap t, σ)
    | none =>
      if isValB fn then
        match firstTrap? args with
        | some t => some (.trap t, σ)
        | none =>
          if isValListB args then
            match asLam? fn with
            | some (_, ps, _, body) =>
              if args.length == ps.length then
                some (substMany (zipParams ps args) body, σ)
              else none
            | none => none
          else
            match stepListOnce Δ Φ args σ with
            | some (args', σ') => some (.apply fn args', σ')
            | none => none
      else
        match stepOnce Δ Φ fn σ with
        | some (fn', σ') => some (.apply fn' args, σ')
        | none => none
  | .applyDir name args, σ =>
    match firstTrap? args with
    | some t => some (.trap t, σ)
    | none =>
      if isValListB args then
        match Φ name with
        | some fd =>
          if args.length == fd.params.length then
            some (substMany (zipParams fd.params args) fd.body, σ)
          else none
        | none => none
      else
        match stepListOnce Δ Φ args σ with
        | some (args', σ') => some (.applyDir name args', σ')
        | none => none
  | .un op e1, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      match asLit? e1 with
      | some l =>
        match evalUnOp op l with
        | some l' => some (.lit l', σ)
        | none => none
      | none =>
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.un op e1', σ')
        | none => none
  | .bin op e1 e2, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      if op = .and then
        match asBoolLit? e1 with
        | some false => some (.lit (.bool false), σ)
        | some true => some (e2, σ)
        | none =>
          match stepOnce Δ Φ e1 σ with
          | some (e1', σ') => some (.bin op e1' e2, σ')
          | none => none
      else if op = .or then
        match asBoolLit? e1 with
        | some true => some (.lit (.bool true), σ)
        | some false => some (e2, σ)
        | none =>
          match stepOnce Δ Φ e1 σ with
          | some (e1', σ') => some (.bin op e1' e2, σ')
          | none => none
      else if isValB e1 then
        match asTrap? e2 with
        | some t => some (.trap t, σ)
        | none =>
          if isValB e2 then
            match asLit? e1, asLit? e2 with
            | some l1, some l2 =>
              match evalBinOp op l1 l2 with
              | some (.val l') => some (.lit l', σ)
              | some (.trap t) => some (.trap t, σ)
              | none => none
            | _, _ => none
          else
            match stepOnce Δ Φ e2 σ with
            | some (e2', σ') => some (.bin op e1 e2', σ')
            | none => none
      else
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.bin op e1' e2, σ')
        | none => none
  | .let_ x e1 e2, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      if isValB e1 then
        some (subst x e1 e2, σ)
      else
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.let_ x e1' e2, σ')
        | none => none
  | .if_ c t e2, σ =>
    match asTrap? c with
    | some tr => some (.trap tr, σ)
    | none =>
      match asBoolLit? c with
      | some true => some (t, σ)
      | some false => some (e2, σ)
      | none =>
        match stepOnce Δ Φ c σ with
        | some (c', σ') => some (.if_ c' t e2, σ')
        | none => none
  | .while_ c b, σ =>
    some (.if_ c (.block [b, .while_ c b]) (.lit .unit), σ)
  | .match_ s arms, σ =>
    match asTrap? s with
    | some t => some (.trap t, σ)
    | none =>
      if isValB s then
        match arms with
        | [] => some (.trap .matchFailure, σ)
        | (p, body) :: rest =>
          match matchPat p s with
          | some env => some (substMany env body, σ)
          | none => some (.match_ s rest, σ)
      else
        match stepOnce Δ Φ s σ with
        | some (s', σ') => some (.match_ s' arms, σ')
        | none => none
  | .makeData adt tag es, σ =>
    match firstTrap? es with
    | some t => some (.trap t, σ)
    | none =>
      match stepListOnce Δ Φ es σ with
      | some (es', σ') => some (.makeData adt tag es', σ')
      | none => none
  | .getTag e1, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      match asMakeData? e1 with
      | some (_, tag, vs) =>
        if isValListB vs then some (.lit (.int (Int32.ofNat tag)), σ)
        else
          match stepOnce Δ Φ e1 σ with
          | some (e1', σ') => some (.getTag e1', σ')
          | none => none
      | none =>
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.getTag e1', σ')
        | none => none
  | .cellNew e1, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      if isValB e1 then
        some (.loc σ.length, σ ++ [e1])
      else
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.cellNew e1', σ')
        | none => none
  | .cellGet e1, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      match asLoc? e1 with
      | some l =>
        match σ[l]? with
        | some v => some (v, σ)
        | none => none
      | none =>
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.cellGet e1', σ')
        | none => none
  | .cellSet e1 e2, σ =>
    match asTrap? e1 with
    | some t => some (.trap t, σ)
    | none =>
      if isValB e1 then
        match asTrap? e2 with
        | some t => some (.trap t, σ)
        | none =>
          if isValB e2 then
            match asLoc? e1 with
            | some l =>
              if l < σ.length then some (.lit .unit, σ.set l e2)
              else none
            | none => none
          else
            match stepOnce Δ Φ e2 σ with
            | some (e2', σ') => some (.cellSet e1 e2', σ')
            | none => none
      else
        match stepOnce Δ Φ e1 σ with
        | some (e1', σ') => some (.cellSet e1' e2, σ')
        | none => none
  | _, _ => none
termination_by e _ => sizeOf e

def stepListOnce (Δ : AdtEnv) (Φ : FunEnv) : List Expr → Store → Option (List Expr × Store)
  | [], _ => none
  | e :: rest, σ =>
    if isValB e then
      match stepListOnce Δ Φ rest σ with
      | some (rest', σ') => some (e :: rest', σ')
      | none => none
    else
      match stepOnce Δ Φ e σ with
      | some (e', σ') => some (e' :: rest, σ')
      | none => none
termination_by es _ => sizeOf es
end

mutual
/-- Every step taken by `stepOnce` is a valid small-step transition in `Semantics.Step`. -/
theorem stepOnce_sound {Δ : AdtEnv} {Φ : FunEnv} {e e' : Expr} {σ σ' : Store}
    (h : stepOnce Δ Φ e σ = some (e', σ')) :
    Step Δ Φ emptyPool e σ e' σ' .none := by
  cases e with
  | lit _ | var _ | loc _ | taskRef _ | syncRef _ _ | lam _ _ _ _
  | spawn _ | await _ | concPrim _ _ | trap _ =>
    unfold stepOnce at h; cases h
  | tuple es =>
    simp only [stepOnce] at h
    cases ht : firstTrap? es with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      exact .tupleTrap (firstTrap?_sound ht)
    | none =>
      rw [ht] at h
      cases hs : stepListOnce Δ Φ es σ with
      | none => rw [hs] at h; cases h
      | some p =>
        rcases p with ⟨es', σ1⟩
        rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
        exact .tupleStep (stepListOnce_sound hs)
  | block es =>
    unfold stepOnce at h
    cases es with
    | nil =>
      injection h with h; injection h with he hσ; subst he hσ
      exact .blockEmpty
    | cons e1 rest =>
      cases rest with
      | nil =>
        injection h with h; injection h with he hσ; subst he hσ
        exact .blockSingle
      | cons e2 tl =>
        dsimp only at h
        cases ht : asTrap? e1 with
        | some t =>
          rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
          rw [asTrap?_sound ht]
          exact .blockConsTrap
        | none =>
          rw [ht] at h; dsimp only at h
          split at h
          · rename_i hv1
            injection h with h; injection h with he hσ; subst he hσ
            exact .blockConsVal (isValB_sound hv1)
          · cases hs : stepOnce Δ Φ e1 σ with
            | none => rw [hs] at h; cases h
            | some p =>
              rcases p with ⟨e1', σ1⟩
              rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
              exact .blockConsStep (stepOnce_sound hs)
  | apply fn args =>
    simp only [stepOnce] at h
    cases htFn : asTrap? fn with
    | some t =>
      rw [htFn] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound htFn]
      exact .applyFnTrap
    | none =>
      rw [htFn] at h; dsimp only at h
      split at h
      · rename_i hvFn
        cases htArgs : firstTrap? args with
        | some t =>
          rw [htArgs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .applyArgsTrap (isValB_sound hvFn) (firstTrap?_sound htArgs)
        | none =>
          rw [htArgs] at h; dsimp only at h
          split at h
          · rename_i hvArgs
            cases hlam : asLam? fn with
            | none => rw [hlam] at h; cases h
            | some q =>
              rcases q with ⟨m, ps, ret, body⟩
              rw [hlam] at h; dsimp only at h
              split at h
              · rename_i hlen
                injection h with h; injection h with he hσ; subst he hσ
                rw [asLam?_sound hlam]
                exact .applyBeta (isValListB_sound hvArgs) (beq_iff_eq.mp hlen)
              · cases h
          · cases hs : stepListOnce Δ Φ args σ with
            | none => rw [hs] at h; cases h
            | some p =>
              rcases p with ⟨args', σ1⟩
              rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
              exact .applyArgs (isValB_sound hvFn) (stepListOnce_sound hs)
      · cases hs : stepOnce Δ Φ fn σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨fn', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .applyFn (stepOnce_sound hs)
  | applyDir name args =>
    simp only [stepOnce] at h
    cases ht : firstTrap? args with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      exact .applyDirTrap (firstTrap?_sound ht)
    | none =>
      rw [ht] at h; dsimp only at h
      split at h
      · rename_i hvArgs
        cases hfd : Φ name with
        | none => rw [hfd] at h; cases h
        | some fd =>
          rw [hfd] at h; dsimp only at h
          split at h
          · rename_i hlen
            injection h with h; injection h with he hσ; subst he hσ
            exact .applyDirBeta hfd (isValListB_sound hvArgs) (beq_iff_eq.mp hlen)
          · cases h
      · cases hs : stepListOnce Δ Φ args σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨args', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .applyDirArgs (stepListOnce_sound hs)
  | un op e1 =>
    simp only [stepOnce] at h
    cases ht : asTrap? e1 with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .unTrap
    | none =>
      rw [ht] at h; dsimp only at h
      cases hl : asLit? e1 with
      | some l =>
        rw [hl] at h; dsimp only at h
        cases hu : evalUnOp op l with
        | none => rw [hu] at h; cases h
        | some l' =>
          rw [hu] at h; injection h with h; injection h with he hσ; subst he hσ
          rw [asLit?_sound hl]
          exact .unVal hu
      | none =>
        rw [hl] at h; dsimp only at h
        cases hs : stepOnce Δ Φ e1 σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .unStep (stepOnce_sound hs)
  | bin op e1 e2 =>
    simp only [stepOnce] at h
    cases ht1 : asTrap? e1 with
    | some t =>
      rw [ht1] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht1]
      exact .binLeftTrap
    | none =>
      rw [ht1] at h; dsimp only at h
      by_cases hand : op = .and
      · subst hand
        simp only [↓reduceIte] at h
        cases hb : asBoolLit? e1 with
        | some b =>
          rw [hb] at h
          cases b <;> dsimp only at h <;>
            injection h with h <;> injection h with he hσ <;> subst he hσ
          · rw [asBoolLit?_sound hb]; exact .binAndFalse
          · rw [asBoolLit?_sound hb]; exact .binAndTrue
        | none =>
          rw [hb] at h; dsimp only at h
          cases hs : stepOnce Δ Φ e1 σ with
          | none => rw [hs] at h; cases h
          | some p =>
            rcases p with ⟨e1', σ1⟩
            rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
            exact .binLeft (stepOnce_sound hs)
      · simp only [hand, ↓reduceIte] at h
        by_cases hor : op = .or
        · subst hor
          simp only [↓reduceIte] at h
          cases hb : asBoolLit? e1 with
          | some b =>
            rw [hb] at h
            cases b <;> dsimp only at h <;>
              injection h with h <;> injection h with he hσ <;> subst he hσ
            · rw [asBoolLit?_sound hb]; exact .binOrFalse
            · rw [asBoolLit?_sound hb]; exact .binOrTrue
          | none =>
            rw [hb] at h; dsimp only at h
            cases hs : stepOnce Δ Φ e1 σ with
            | none => rw [hs] at h; cases h
            | some p =>
              rcases p with ⟨e1', σ1⟩
              rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
              exact .binLeft (stepOnce_sound hs)
        · simp only [hor, ↓reduceIte] at h
          split at h
          · rename_i hv1
            cases ht2 : asTrap? e2 with
            | some t =>
              rw [ht2] at h; injection h with h; injection h with he hσ; subst he hσ
              rw [asTrap?_sound ht2]
              exact .binRightTrap hand hor (isValB_sound hv1)
            | none =>
              rw [ht2] at h; dsimp only at h
              split at h
              · cases hl1 : asLit? e1 with
                | none => rw [hl1] at h; cases h
                | some l1 =>
                  rw [hl1] at h
                  cases hl2 : asLit? e2 with
                  | none => rw [hl2] at h; cases h
                  | some l2 =>
                    rw [hl2] at h; dsimp only at h
                    cases hres : evalBinOp op l1 l2 with
                    | none => rw [hres] at h; cases h
                    | some res =>
                      rw [hres] at h
                      cases res with
                      | val l' =>
                        injection h with h; injection h with he hσ; subst he hσ
                        rw [asLit?_sound hl1, asLit?_sound hl2]
                        exact .binVal hres
                      | trap t =>
                        injection h with h; injection h with he hσ; subst he hσ
                        rw [asLit?_sound hl1, asLit?_sound hl2]
                        exact .binTrap hres
              · cases hs : stepOnce Δ Φ e2 σ with
                | none => rw [hs] at h; cases h
                | some p =>
                  rcases p with ⟨e2', σ1⟩
                  rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
                  exact .binRight hand hor (isValB_sound hv1) (stepOnce_sound hs)
          · cases hs : stepOnce Δ Φ e1 σ with
            | none => rw [hs] at h; cases h
            | some p =>
              rcases p with ⟨e1', σ1⟩
              rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
              exact .binLeft (stepOnce_sound hs)
  | let_ x e1 e2 =>
    simp only [stepOnce] at h
    cases ht : asTrap? e1 with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .letTrap
    | none =>
      rw [ht] at h; dsimp only at h
      split at h
      · rename_i hv1
        injection h with h; injection h with he hσ; subst he hσ
        exact .letVal (isValB_sound hv1)
      · cases hs : stepOnce Δ Φ e1 σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .letStep (stepOnce_sound hs)
  | if_ c t e2 =>
    simp only [stepOnce] at h
    cases ht : asTrap? c with
    | some tr =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .ifTrap
    | none =>
      rw [ht] at h; dsimp only at h
      cases hb : asBoolLit? c with
      | some b =>
        rw [hb] at h
        cases b <;> dsimp only at h <;>
          injection h with h <;> injection h with he hσ <;> subst he hσ
        · rw [asBoolLit?_sound hb]; exact .ifFalse
        · rw [asBoolLit?_sound hb]; exact .ifTrue
      | none =>
        rw [hb] at h; dsimp only at h
        cases hs : stepOnce Δ Φ c σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨c', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .ifStep (stepOnce_sound hs)
  | while_ c b =>
    unfold stepOnce at h
    injection h with h; injection h with he hσ; subst he hσ
    exact .whileUnfold
  | match_ s arms =>
    unfold stepOnce at h
    cases ht : asTrap? s with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .matchScrutTrap
    | none =>
      rw [ht] at h; dsimp only at h
      split at h
      · rename_i hvs
        cases arms with
        | nil =>
          injection h with h; injection h with he hσ; subst he hσ
          exact .matchEmpty (isValB_sound hvs)
        | cons arm rest =>
          rcases arm with ⟨p, body⟩
          dsimp only at h
          cases hm : matchPat p s with
          | some env =>
            rw [hm] at h; injection h with h; injection h with he hσ; subst he hσ
            exact .matchHit (isValB_sound hvs) hm
          | none =>
            rw [hm] at h; injection h with h; injection h with he hσ; subst he hσ
            exact .matchMiss (isValB_sound hvs) hm
      · cases hs : stepOnce Δ Φ s σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨s', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .matchScrut (stepOnce_sound hs)
  | makeData adt tag es =>
    simp only [stepOnce] at h
    cases ht : firstTrap? es with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      exact .makeDataTrap (firstTrap?_sound ht)
    | none =>
      rw [ht] at h
      cases hs : stepListOnce Δ Φ es σ with
      | none => rw [hs] at h; cases h
      | some p =>
        rcases p with ⟨es', σ1⟩
        rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
        exact .makeDataStep (stepListOnce_sound hs)
  | getTag e1 =>
    simp only [stepOnce] at h
    cases ht : asTrap? e1 with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .getTagTrap
    | none =>
      rw [ht] at h; dsimp only at h
      cases hmd : asMakeData? e1 with
      | some q =>
        rcases q with ⟨adt, tag, vs⟩
        rw [hmd] at h; dsimp only at h
        split at h
        · rename_i hvs
          injection h with h; injection h with he hσ; subst he hσ
          rw [asMakeData?_sound hmd]
          exact .getTagVal (isValListB_sound hvs)
        · cases hs : stepOnce Δ Φ e1 σ with
          | none => rw [hs] at h; cases h
          | some p =>
            rcases p with ⟨e1', σ1⟩
            rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
            exact .getTagStep (stepOnce_sound hs)
      | none =>
        rw [hmd] at h; dsimp only at h
        cases hs : stepOnce Δ Φ e1 σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .getTagStep (stepOnce_sound hs)
  | cellNew e1 =>
    simp only [stepOnce] at h
    cases ht : asTrap? e1 with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .cellNewTrap
    | none =>
      rw [ht] at h; dsimp only at h
      split at h
      · rename_i hv1
        injection h with h; injection h with he hσ; subst he hσ
        exact .cellNewVal (isValB_sound hv1)
      · cases hs : stepOnce Δ Φ e1 σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .cellNewStep (stepOnce_sound hs)
  | cellGet e1 =>
    simp only [stepOnce] at h
    cases ht : asTrap? e1 with
    | some t =>
      rw [ht] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht]
      exact .cellGetTrap
    | none =>
      rw [ht] at h; dsimp only at h
      cases hloc : asLoc? e1 with
      | some l =>
        rw [hloc] at h; dsimp only at h
        cases hl : σ[l]? with
        | none => rw [hl] at h; cases h
        | some v =>
          rw [hl] at h; injection h with h; injection h with he hσ; subst he hσ
          rw [asLoc?_sound hloc]
          exact .cellGetVal hl
      | none =>
        rw [hloc] at h; dsimp only at h
        cases hs : stepOnce Δ Φ e1 σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .cellGetStep (stepOnce_sound hs)
  | cellSet e1 e2 =>
    simp only [stepOnce] at h
    cases ht1 : asTrap? e1 with
    | some t =>
      rw [ht1] at h; injection h with h; injection h with he hσ; subst he hσ
      rw [asTrap?_sound ht1]
      exact .cellSetLeftTrap
    | none =>
      rw [ht1] at h; dsimp only at h
      split at h
      · rename_i hv1
        cases ht2 : asTrap? e2 with
        | some t =>
          rw [ht2] at h; injection h with h; injection h with he hσ; subst he hσ
          rw [asTrap?_sound ht2]
          exact .cellSetRightTrap (isValB_sound hv1)
        | none =>
          rw [ht2] at h; dsimp only at h
          split at h
          · rename_i hv2
            cases hloc : asLoc? e1 with
            | none => rw [hloc] at h; cases h
            | some l =>
              rw [hloc] at h; dsimp only at h
              split at h
              · rename_i hlt
                injection h with h; injection h with he hσ; subst he hσ
                rw [asLoc?_sound hloc]
                exact .cellSetVal hlt (isValB_sound hv2)
              · cases h
          · cases hs : stepOnce Δ Φ e2 σ with
            | none => rw [hs] at h; cases h
            | some p =>
              rcases p with ⟨e2', σ1⟩
              rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
              exact .cellSetRight (isValB_sound hv1) (stepOnce_sound hs)
      · cases hs : stepOnce Δ Φ e1 σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1', σ1⟩
          rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
          exact .cellSetLeft (stepOnce_sound hs)
termination_by sizeOf e

theorem stepListOnce_sound {Δ : AdtEnv} {Φ : FunEnv} {es es' : List Expr} {σ σ' : Store}
    (h : stepListOnce Δ Φ es σ = some (es', σ')) :
    StepList Δ Φ emptyPool es σ es' σ' .none := by
  cases es with
  | nil => simp [stepListOnce] at h
  | cons e rest =>
    simp only [stepListOnce] at h
    split at h
    · rename_i hv
      cases hs : stepListOnce Δ Φ rest σ with
      | none => rw [hs] at h; cases h
      | some p =>
        rcases p with ⟨rest', σ1⟩
        rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
        exact .tail (isValB_sound hv) (stepListOnce_sound hs)
    · cases hs : stepOnce Δ Φ e σ with
      | none => rw [hs] at h; cases h
      | some p =>
        rcases p with ⟨e', σ1⟩
        rw [hs] at h; injection h with h; injection h with he hσ; subst he hσ
        exact .head (stepOnce_sound hs)
termination_by sizeOf es
end

/-- Fuel-bounded deterministic multi-step evaluator. -/
def runSteps (Δ : AdtEnv) (Φ : FunEnv) : Nat → Expr → Store → Except String (Expr × Store)
  | fuel, e, σ =>
    if isValB e then
      .ok (e, σ)
    else
      match fuel with
      | 0 => .error "evaluation fuel exhausted"
      | fuel' + 1 =>
        match asTrap? e with
        | some t => .error s!"runtime trap: {repr t}"
        | none =>
          match stepOnce Δ Φ e σ with
          | some (e', σ') => runSteps Δ Φ fuel' e' σ'
          | none => .error s!"cannot step expression in pure evaluator: {repr e}"

/-- **Soundness of Executable Evaluator (`runSteps_sound`)**:
    Every value returned by `runSteps` is a valid `IsValue` reached via a
    machine-checked `Steps` transition sequence in `CoreGeisha.Semantics`. -/
theorem runSteps_sound {Δ : AdtEnv} {Φ : FunEnv} {fuel : Nat} {e v : Expr} {σ σ' : Store}
    (h : runSteps Δ Φ fuel e σ = .ok (v, σ')) :
    IsValue v ∧ Steps Δ Φ e σ v σ' := by
  induction fuel generalizing e σ with
  | zero =>
    unfold runSteps at h
    split at h
    · rename_i hv
      injection h with h; injection h with he hσ; subst he hσ
      exact ⟨isValB_sound hv, .refl _ _⟩
    · cases h
  | succ fuel' ih =>
    unfold runSteps at h
    split at h
    · rename_i hv
      injection h with h; injection h with he hσ; subst he hσ
      exact ⟨isValB_sound hv, .refl _ _⟩
    · cases ht : asTrap? e with
      | some _ => rw [ht] at h; cases h
      | none =>
        rw [ht] at h; dsimp only at h
        cases hs : stepOnce Δ Φ e σ with
        | none => rw [hs] at h; cases h
        | some p =>
          rcases p with ⟨e1, σ1⟩
          rw [hs] at h
          rcases ih h with ⟨hv, hsteps⟩
          exact ⟨hv, .trans (stepOnce_sound hs) hsteps⟩

/-- Render a terminal Core Geisha `Expr` value for CLI differential comparison. -/
def formatEvalValue : Expr → String
  | .lit (.int n) => toString n
  | .lit (.int64 n) => toString n
  | .lit (.bool true) => "true"
  | .lit (.bool false) => "false"
  | .lit (.char c) => toString c
  | .lit (.str s) => s
  | .lit .unit => "()"
  | other => reprStr other

end CoreGeisha
