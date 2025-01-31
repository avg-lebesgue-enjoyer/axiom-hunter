/-
  **File:** `AxiomHunter/UI/Output.lean`

  **Purpose:**
    Display the list of primitive justifications that each statement ultimately depends on.
-/

/- IMPORTS: -/

import AxiomHunter.DependencyBackend
import AxiomHunter.UI.Statements
import AxiomHunter.UI.ProofDependencies



open AxiomHunter
/- SECTION: Building in the dependencies -/
-- Do not edit any code here.

/-- Print the `Primitive` dependencies for the given `Statement`. -/
def Statement.printCurrentDependencies (s : Statement) : IO Unit := s.printDependencies proofs
@[inherit_doc Statement.printCurrentDependencies]
def Statement.pd : Statement → IO Unit := Statement.printCurrentDependencies
/-- Print all the `Primitive` dependencies for the given `List` of `Statement`s. -/
def List.printAllDependencies (xs : List Statement) : IO Unit := do
  for x in xs do
    IO.println s!"========\n{Terminal.styleProving "Proving"} rule {x.toString}\n========"
    x.printCurrentDependencies
    IO.print "\n"



/- LAUNCH: List which things you'd like to see the axioms for here, please! -/

-- TODO: Make this an interactive thing at the command line where you can repeatedly provide a name and receive a list of
--        primitive justifications. cba right now.
def AxiomHunter.printEm : IO Unit := List.printAllDependencies
  [ -- List the `Statement`s whose proof dependencies you would like to see here.
    -- *Example:*
    --  `  my_statement1 `
    --  `, my_statement2 `
    --  `, my_statement3 `
    --  `, my_statement4 `
    my_statement1
  , my_statement2
  , my_statement3
  , my_statement4
  ]
