# Coq Actions

This repository contains the machinized proof using the Coq Proof Assistant for Theorem 1 in Section 3. 
- `ActionDefinitions.v` contains the definition of actions according to Definition 1.
- `ActionDefinitionsB.v` contains equivalent definition for boolean logic.
- `ActionEquivalence.v` contains the proof for Theorem 1, and further Lemmata and Theorems needed.
- `ActionStructuralEquality.v` contains Theorems and Lemmata about structural equality of actions.

## Execution

To execute the proof you need to have the latest Coq Platform installed. Installation files can be found [here](https://github.com/coq/platform/releases/tag/2023.11.0).
Make sure to activate the association between -.v files and COQ-IDE. 

The files depend on each other and thus need to be compiled in the right order.
- Start by opening `ActionsDefinitions.v` with *CoqIDE*. Go to menu `Compile -> Compile Buffer`.
  This should create an output that looks like this:
  ```
  Running: coqc "-topfile" "...\coq-actions\ActionDefinitions.v" "...\coq-actions\ActionDefinitions.v" 2>&1
  ```
  New files should appear in the folder:
  ```
  ActionDefinitions.vo
  ActionDefinitions.vok
  ActionDefinitions.vos
  ```
- Next, open `ActionStructuralEquality.v` also with *CoqIDE*. Compile the file using `Compile -> Compile Buffer`.
- Repeat the step for `ActionDefinitionsB.v`, then `ActionEquivalence.v`.
