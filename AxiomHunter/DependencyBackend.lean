/-
  **File:** `AxiomHunter/DependencyBackend.lean`

  **Purpose:**
    Library for registering statements and dependencies for their proofs, and for eventually finding the list of primitive
    dependencies required to prove any registered statement (according to the supplied proof dependencies).
-/

/- SECTION: Terminal colouring escape codes -/

namespace Terminal
  /-- Escape sequence to reset terminal colouring. -/
  def reset : String := "\u001b[0m"
  /-- Escape sequence to colour the *name* of a `Statement`. -/
  def styleName (it : String) : String := s!"\u001b[1;4;94m{it}{reset}"
  /-- Escape sequence to style the *description* of a `Statement`. -/
  def styleDescription (it : String) : String := s!"\u001b[0m{it}{reset}"
  /-- Escape sequence to colour the declaration that something is justified as an `ax`iom. -/
  def styleAxiom (it : String) : String := s!"\u001b[1;95m{it}{reset}"
  /-- Escape sequence to colour the declaration that something is justified as a `defn`ition. -/
  def styleDefinition (it : String) : String := s!"\u001b[1;96m{it}{reset}"
  /-- Escape sequence to colour the declaration that something is `unproven`. -/
  def styleUnproven (it : String) : String := s!"\u001b[1;91m{it}{reset}"
  /-- Escape sequence to colour the declaration that we are proving something. -/
  def styleProving (it : String) : String := s!"\u001b[1;92m{it}{reset}"
end Terminal



/- SECTION: Tools for and lemmas about `List`s -/

abbrev NonEmptyList.{u} (α : Type u) := { xs : List α // xs ≠ [] }
theorem NonEmptyList.of_cons.{u} {α : Type u} : ∀ {x : α} {xs : List α}, (x :: xs) ≠ [] := by
  intros
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨(x :: xs), NonEmptyList.of_cons⟩

/-- Print out a list nicely. -/
def List.print [ToString α] (xs : List α) : IO Unit := do
  for x in xs do
    IO.println x

/--
  Given `(xs ys : List α)`, `xs.nub' ys` removes all duplicates of `xs` and all elements of `xs` which
  occur in `ys`.
-/
-- TODO: This is inefficient (`ys.contains x` is `𝒪(|ys|)`, and thus `List.nub' xs ys ∈ 𝒪(|xs| * |ys|)`).
--       Implementing this method with an `𝒪(1)`-lookup-time `Set` data structure would be better
--        (for larger projects).
def List.nub' [BEq α] : List α → List α → List α
  | [], ys => ys
  | (x :: xs), ys => if ys.contains x then xs.nub' ys else xs.nub' (x :: ys)
/-- Remove all duplicates from a given `List`. -/
def List.nub [BEq α] : List α → List α := (List.nub' · [])

def List.mem_nub'_right [BEq α] : ∀ (xs ys : List α) (y : α), y ∈ ys → y ∈ xs.nub' ys := by
  intro xs ; induction xs
  case nil =>
    intros
    unfold List.nub'
    assumption
  case cons x xs ih =>
    intro ys y h_y_in_ys
    unfold List.nub'
    split
    case isTrue =>
      apply ih ys y
      assumption
    case isFalse =>
      apply ih (x :: ys) y
      simp only [mem_cons, ‹y ∈ ys›, or_true]

def List.nub'_nonempty_of_right_nonempty [BEq α] : ∀ (xs : List α) (ys : List α),  xs ≠ [] → xs.nub' ys ≠ [] := by
  intro xs ys h_xs_nonempty
  cases h_xs_rep : xs
  case nil =>
    contradiction -- `x = []` and `x ≠ []`
  case cons x xs =>
    unfold List.nub'
    split
    case isTrue h_ys_contains_x =>
      have ⟨y, h_y_in_ys, _⟩ := List.contains_iff_exists_mem_beq.mp h_ys_contains_x
      have : y ∈ xs.nub' ys := List.mem_nub'_right xs ys y h_y_in_ys
      have : xs.nub' ys ≠ [] := by
        intro h
        rw [h] at this
        contradiction
      exact this
    case isFalse h_n_ys_contains_x =>
      have : x ∈ xs.nub' (x :: ys) := List.mem_nub'_right xs (x :: ys) x (by simp)
      have : xs.nub' (x :: ys) ≠ [] := by
        intro h
        rw [h] at this
        contradiction
      exact this

def List.nub_nonempty [BEq α] (xs : List α) : xs ≠ [] → xs.nub ≠ [] := by
  intro h_xs_nonempty
  unfold List.nub
  apply List.nub'_nonempty_of_right_nonempty
  assumption



/- SECTION: Data structures: `Statement`s, `Primitive`s and `ProofDependency`s. -/

/--
  A statement, decoupled from any particular proof.

  When `def`ining new statements, do them as follows:
  ```lean4
    @[match_pattern] def my_statement : Statement := ⟨"my_statement", "my_description"⟩
  ```
  This is so that the `Statement.proof` function can pattern-match on the statement

  **Field `name : String`**
    A short name by which to reference the statement. Ideally equal to the internal `Lean.Name` given to the
    defined statement. Used when displaying `Statement`s.

  **Field `description : String`**
    A long, precise description of the statement. This should be written in appropriate mathematical notation;
    e.g. `∃x, x + 1 = 3`. Sometimes used when displaying `Statement`s.
-/
-- TODO: Automate making the `name` field match the `def`'s `Lean.Name` in a way compatible with nice uses of
--        `@[match_pattern]` (i.e. so that `Statement.proof` can indeed pattern-match on it.)
structure Statement : Type where
  name        : String
  description : String
deriving Repr
namespace Statement
  /-- Pointwise equality of `Statement`s. -/
  def beq (r s : Statement) : Bool :=
    r.name = s.name ∧ r.description = s.description
  instance Statement.instBEq : BEq Statement where beq := Statement.beq
  instance : LawfulBEq Statement where
  rfl := by
    intro s
    show (s.beq s) = true
    simp only [Statement.beq, and_self, decide_True]
  eq_of_beq := by
    intro r s (h : r.beq s = true)
    simp only [Statement.beq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h
    match r, s with
    | Statement.mk nr dr , Statement.mk ns ds =>
      simp_all only

  /-- A suitable representation of a `Statement` to be printed on the command-line or Infoview. -/
  def toString (s : Statement) : String := s!"{Terminal.styleName s.name}:\n  {Terminal.styleDescription s.description}"
  instance instToString : ToString Statement where toString := Statement.toString

  /-- Print a suitable representation of a `Statement` to `IO.stdout`. -/
  def print : Statement → IO Unit := IO.println ∘ Statement.toString

  /-- Compare `Statement`s by their `name`s, made lowercase. -/
  def ble (r s : Statement) : Bool := r.name.toLower ≤ s.name.toLower
end Statement

def List.asNames : List Statement → List String := map Statement.name

/--
  A primitive justification for a specified `Statement`.

  **Parameter `(s : Statement)`**
    The statement which is being primitively justified

  **Constructor `ax : Primitive s`**
    Recognition that `s` should be taken as an axiom.

  **Constructor `defn : Statement → Primitive`**
    Recognition that `s` should be regarded as a definition.

  **Constructor `unproven : Statement → Primitive`**
    Recognition that `s` should be regarded as yet unproven.
    `Primitive.unproven`s look jarring when printed, so they're hard to miss.
-/
inductive Primitive (s : Statement) : Type where
  | ax : Primitive s
  | defn : Primitive s
  | unproven : Primitive s
deriving Repr, BEq

/--
  A primitive justification for some `Statement`.

  **Field `(statement : Statement)`**
    The statement being justified.

  **Field `(primitive : Primitive statement)`**
    The justification being encapsulated in this record.
-/
structure AnyPrimitive : Type where
  statement : Statement
  primitive : Primitive statement
deriving Repr, BEq

namespace Primitive
  /-- Retrieve the `Statement` which this `Primitive` justifies. -/
  def getStatement {s : Statement} : Primitive s → Statement := fun _ => s
end Primitive

/--
  A record of the dependencies necessary to construct a proof of a `Statement`.

  **Constructor `primitive : {s : Statement} → (p : Primitive) → s = p.getStatement → ProofDependencies`**
    A record that `s` can be proven by taking it as a primitive `p`. The `s = p.getStatement` argument
    ensures that the primitive indeed constrains `s`.

  **Constructor `deduction : {goal : Statement} → (premises : NonEmptyList Statement) → ProofDependencies`**
    A record that a proof of the given `goal` can be proven using the `Statements` listed in the `premises`.
    The onus is on the user to ensure that the `goal` can indeed be proven using the `premises`.
-/
inductive ProofDependencies : Type where
  | primitive : (s : Statement) → (p : Primitive s) → s = p.getStatement → ProofDependencies
  | deduction : (_ : Statement) → NonEmptyList Statement → ProofDependencies

namespace Primitive
  /-- A suitable representation of a `Primitive` justification to be printed on the comand-line or Infoview. -/
  def toString {s : Statement} : Primitive s → String
    | ax => s!"{Terminal.styleAxiom "Ax:"}  {s.toString}"
    | defn => s!"{Terminal.styleDefinition "Def:"} {s.toString}"
    | unproven => s!"{Terminal.styleUnproven "UNPROVEN!"}: {s.toString}"
  instance instToString {s : Statement} : ToString (Primitive s) where toString := Primitive.toString
end Primitive
namespace AnyPrimitive
  /-- A suitable representation of an `AnyPrimitive` justification to be printed on the comand-line or Infoview. -/
  def toString (p : AnyPrimitive) : String := p.primitive.toString
  instance instToString : ToString AnyPrimitive where toString := AnyPrimitive.toString

  /--
    Compare `AnyPrimitive`s by lexicographic order: sort by the `Primitive` constructor
    (`unproven` < `ax` < `defn`), breaking ties by the `Statement`.

    **Param `(p : AnyPrimitive)`**
      First `AnyPrimitive` to compare.

    **Param `(q : AnyPrimitive)`**
      Second `AnyPrimitive` to compare.

    **Returns `: Prop`**
      `true` just when `p` is lexicographically less-or-equal to `q`, as described above.
  -/
  def ble : AnyPrimitive → AnyPrimitive → Bool
    | ⟨r, .unproven⟩, ⟨s, .unproven⟩  => r.ble s
    | ⟨_, .unproven⟩, _               => true
    | ⟨r, .ax⟩,       ⟨s, .ax⟩        => r.ble s
    | ⟨_, .ax⟩,       ⟨_, .defn⟩      => true
    | ⟨r, .defn⟩,     ⟨s, .defn⟩      => r.ble s
    | _,              _               => false
end AnyPrimitive

namespace Statement
  /--
    Get a `List` of `Primitive` dependencies for a given `Statement`, assuming some known `proofs` of statements.
    This recursively searches through the dependencies of the relevant `proofs` too. Because this is a `partial`
    function, a call to `Statement.getDependencies` may fail to terminate if there is a circular proof registered
    in the given `proofs`.

    The returned `List` should be **nonempty**. I haven't gotten around to proving that it is indeed nonempty yet.
    If you find the `List` to be empty, then this is a bug.

    **Param `(proofs : Statement → ProofDependencies)`**
      A function cataloguing the dependencies of known proofs.
    **Param `(s : Statement)`**
      The `Statement` to get a list of `Primitive` dependencies for
    **Returns `List Primitive`**
      A `List` of `Primitive`s that `s` ultimately depends on, using the given `proofs`.
  -/
  -- TODO: Make the return type here `NonEmptyList` rather than `List`.
  partial def getDependencies (proofs : Statement → ProofDependencies) (s : Statement) : List AnyPrimitive :=
    match proofs s with
    | .primitive s p _ => [⟨s, p⟩]
    | .deduction _ ⟨xs, _⟩ =>
      xs.flatMap (List.nub ∘ getDependencies proofs) |> List.nub |> (List.mergeSort (le := AnyPrimitive.ble))
end Statement

namespace Statement
  def printDependencies (proofs : Statement → ProofDependencies) : Statement → IO Unit :=
    List.print ∘ getDependencies proofs
end Statement
