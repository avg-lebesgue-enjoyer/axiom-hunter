/-
  **File:** `AxiomHunter/UI/ProofDependencies.lean`

  **Purpose:**
    Users should register all proof dependencies here.
-/

/- IMPORTS: -/

import AxiomHunter.DependencyBackend
import AxiomHunter.UI.Statements



namespace AxiomHunter -- to prevent name collisions with Lean standard libraries
/- LAUNCH: List your proof dependencies here, please! -/

def proofs : Statement → ProofDependencies
  -- **Your proof dependencies go here**
  -- *Example:*
  --  -- An example primitive justification, here justified by `.ax`. You can use `.defn` if you want, too.
  --  ` | s@my_statement1 => .primitive s .ax rfl         ` -- *The trailing `rfl` is necessary on any `.primitive`*
  --  -- Two example deductions of a statement from other statements. The list in each case can contain multiple elements.
  --  ` | s@my_statement2 => .deduction s [my_statement1] ` -- *Repeating the statement `s` is necessary in every pattern-match*
  --  ` | s@my_statement4 => .deduction s [my_statement3] `
  -- All `Statement`s you registered in `AxiomHunter/UI/Statements.lean` should have the `match_pattern` attribute
  --  so that they may be pattern-matched here.
  | s@my_statement1 => .primitive s .ax rfl
  | s@my_statement2 => .deduction s [my_statement1]
  | s@my_statement4 => .deduction s [my_statement3]

  -- *This final line should not be modified.* It signifies that everything not proven above is indeed unproven
  | s@(_) => .primitive s .unproven rfl

-- With the example setup above, the following lines should produce outputs as listed below each.
-- (Note: The output may be polluted with plaintext "escape" sequences designed to be used with my `zsh` terminal.
--        Don't mind that unless they do indeed appear broken when you compile and run this project.)
-- ` #eval my_statement1.printDependencies proofs `
--    *`Ax:  my_statement1: `*
--    *`  my_description1   `*
-- ` #eval my_statement2.printDependencies proofs `
--    *`Ax:  my_statement1: `*
--    *`  my_description1   `*
-- ` #eval my_statement3.printDependencies proofs `
--    *`UNPROVEN!:  my_statement3: `*
--    *`  my_description3                 `*
-- ` #eval my_statement4.printDependencies proofs `
--    *`UNPROVEN!:  my_statement3: `*
--    *`  my_description3                 `*
