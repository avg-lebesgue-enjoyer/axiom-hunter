# AxiomHunter
A simple system for recording statements and dependencies among them. This tool was designed to back-track from large theorems to find what axioms they ultimately depend upon (hence the name `AxiomHunter`).

I probably won't maintain this repository for very long; it currently does *enough* for me to use the tool, and that's all that matters to me right now.

## Model
`AxiomHunter` is comprised of three main data types:
- **`Statement`s**, which capture mathematical statements.
- **`Primitive` justifications**, which are basic assertions that certain `Statements` are to be justified without further dependencies. These cover `ax`ioms and `defn`itions, and a special error case for `unproven` statements.
- **`ProofDependencies`**, which record that some `s : Statement` may be justified by a `Primitive` justification, or by a proof✝ which uses a non-empty `List` of other `Statement`s. Giving a list `[x₀, x₁, ..., xₐ] : List Statement` as justification for `s` is tantamount to saying that `x₀ ∧ x₁ ∧ ⋯ ∧ xₐ → s`.

To make the tool useful, there is a function (`Statement.getDependencies`) which, provided a statement `s`, recursively searches through its `ProofDependencies` to collect a list of all `Primitive` justifications underlying the recorded proof of `s`.

In principle, this tool can be used in the following more general context. We assume three classes of objects:
- **Node**s; these are implemented as `Statement`s,
- **Primitive**s which assert that certain **Node**s are reachable; these are implemented as `Primitive` justifications,
- **Rule**s which describe when each **Node** is reachable — either by a **Primitive** or by first reaching a nonempty list of other **Node**s; these are implemented as `ProofDependencies`.
This tool is then equipped with a function that, given the above setup and a starting node `n`, is able to find all **Primitive**s which are used to reach `n`.

✝This data structure **does not** record the *proof* itself; it merely records the promise that the user indeed has such a proof. The purpose of this tool is to help efficiently search for axioms; it is not to perform slow and precise formal verification.

## Actually using the tool
1. Edit `./AxiomHunter/UI/Statements.lean` and add all your `Statement`s there, as illustrated by the example. See that file for further details.
2. Edit `./AxiomHunter/UI/ProofDependencies.lean` and add all your justifications for each `Statement` there. Any statements you do not list will be justified by a `Primitive.unproven`, which you will be able to see clearly in the program's output. See that file for further details. **CHECK FOR YOURSELF THAT YOU DO NOT ENCODE ANY CYCLIC PROOFS** — I was too lazy to build in my own cycle detection (this is first on the todo list for future development, if that ever happens).
3. Edit `./AxiomHunter/UI/Output.lean` and list all of the `Statement`s you wish to see the ultimate `Primitive` justifications for.
4. Build the project (run `lean build` from the command line at this directory).
5. Run the generated executable (run `.lake/build/bin/axiomhunter` from the command line at this directory). All that you desire shall be printed on-screen.
6. Repeat steps (2.) to (5.) until you've learned something interesting about the structure of your newly encoded theory.

## Contributions
Idk how to use GitHub, and I'm not even all that great with Lean yet. If you want to contribute, feel free to fork this repository.

## Copyright
Idc. Go nuts. Not like I have the funds for a lawyer anyway ;)
