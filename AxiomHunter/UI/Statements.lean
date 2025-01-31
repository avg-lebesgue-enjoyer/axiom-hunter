/-
  **File:** `AxiomHunter/UI/Statements.lean`

  **Purpose:**
    Users should register all statements here.
-/

/- IMPORTS: -/

import AxiomHunter.DependencyBackend



namespace AxiomHunter
/- LAUNCH: List your statements here, please! -/

-- **Your list of statements goes here.**
-- *Example:*
--  ` @[match_pattern] def my_statement1 : Statement := ⟨"my_statement1", "my_description1"⟩  `
--  ` @[match_pattern] def my_statement2 : Statement := ⟨"my_statement2", "my_description2"⟩  `
--  ` @[match_pattern] def my_statement3 : Statement := ⟨"my_statement3", "my_description3"⟩  `
--  ` @[match_pattern] def my_statement4 : Statement := ⟨"my_statement4", "my_description4"⟩  `
-- The first string you provide should be the same as the identifier you give to Lean
--  (e.g. `"my_statement1"` and `my_statement1` etc. above). Slight variations are okay
--  (e.g. if you want to cite a source in the string).
--  `AxiomHunter` only prints out the *string* you provide. If the string is dissimilar
--  to the identifier, you may have a hard time finding the identifier to chase down later.
@[match_pattern] def my_statement1 : Statement := ⟨"my_statement1", "my_description1"⟩
@[match_pattern] def my_statement2 : Statement := ⟨"my_statement2", "my_description2"⟩
@[match_pattern] def my_statement3 : Statement := ⟨"my_statement3", "my_description3"⟩
@[match_pattern] def my_statement4 : Statement := ⟨"my_statement4", "my_description4"⟩
