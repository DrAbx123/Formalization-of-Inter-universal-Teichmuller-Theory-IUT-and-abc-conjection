# Working Principles for This Project

## 1. Work Incrementally

- Do not repeatedly re-audit the same ground. Inspect what is needed for the current task and move the proof forward.
- The IUT project is very large. No single agent can hold the entire project in mind or control it globally. Work through focused, concrete patches that improve the current area.
- Keep changes as small and local as the task allows. Preserve working code and avoid unnecessary rewrites.

## 2. Keep an Append-Only Research Log

- Take notes frequently and record research as soon as it produces a useful fact, decision, failed attempt, or proof result.
- The purpose of notes is to know exactly what was changed and why. Do not erase earlier notes and replace them with a new summary; that destroys history.
- Treat the notes as an external memory. Do not rely on being able to remember complex investigations later. Before starting related work, consult the existing notes and reuse their conclusions.
- Add new entries to the existing record. Correct an earlier conclusion only when there is clear evidence, and preserve the superseded entry with an explanation of the correction.

## 3. Respect Verified Mathematics

- Reuse previously established lemmas, definitions, and proof strategies whenever possible.
- Minimize overturning earlier conclusions. In Lean, code that compiles is a proved theorem; do not disturb such code without a specific mathematical or engineering reason.
- Prefer a narrowly targeted patch over a broad refactor, especially in code that already compiles.

## 4. Follow the Steps Completely

- Work in an explicit sequence: understand the local context, state the next subgoal, make the smallest useful change, compile it, record the result, and then proceed.
- Do not skip difficult steps or hide unfinished work behind presentation. When a step is hard, investigate it and overcome the difficulty directly.
- The goal is clean, completed mathematics and maintainable Lean code. Either do the requested work or state plainly that it cannot be done; do not substitute decorative process for progress.

## 5. Use Deliberate, Distinguishable Names

- Every definition, theorem, lemma, proposition, structure, namespace, variable, and supporting declaration must have a meaningful and distinguishable name.
- Choose names that communicate the mathematical object or result and fit the naming conventions already established in the surrounding code.
- Do not use arbitrary, vague, disposable, or collision-prone names such as `foo`, `bar`, `test`, `tmp`, or unexplained numeric suffixes.
- Before introducing a name, check the local namespace and nearby files for existing declarations and choose a name that cannot be confused with them.
- If a temporary name is unavoidable during exploration, replace it with a precise permanent name before considering the work complete.

## 6. State Claims Precisely and Proportionally

- Never expand a theorem, method, hypothesis, or project result beyond what has actually been proved or tested. State the exact assumptions, objects, and scope.
- Be honest about whether a conclusion is strong or weak. Do not present a local, conditional, or partial result as a general, definitive, or project-wide result.
- Treat generalization as a mathematical claim that requires a valid, reusable argument. Do not claim broader applicability merely because a proof works in one instance; if the method is not known to generalize, say so.
- Research notes must be factual and proportionate. Record evidence, limitations, open cases, and failed attempts instead of using emphatic language or overstating progress.
- Do not use absolute progress statements or predictions such as "this is the final verification" or "all changes are complete" without concrete evidence that supports that exact claim.
- Describe status with verifiable facts: identify the files or theorems checked, the commands that passed, the cases that remain, and any uncertainty. Update the statement when new evidence changes the scope.

## 7. Do Not Build on Unproved Foundations

- Do not use an unproved theorem, placeholder declaration, `sorry`, fabricated axiom, or merely promised interface field as the foundation for later mathematics.
- An absent theorem is a real proof gap, not a component that can be made to look ready by reserving fields for it. Do not describe such scaffolding as progress toward a proved result.
- Prove every required theorem before using it as a dependency for the next step, and compile the dependent code against that actual proof.
- If the required theorem cannot yet be proved, record the precise mathematical gap and do not advance the dependent argument on a fictitious basis. Continue only with work that is genuinely independent and clearly separated from that gap.

## 8. Build Theorems from the Bottom Up

- Construct the theory in dependency order, starting with the definitions, propositions, and lemmas on which later theorems rely.
- Before proving or using a theorem, verify that every required assumption is stated precisely and has itself been proved or otherwise validly established in the current context.
- If any required assumption is false, unavailable, or unproved, stop the dependent line of work immediately. Do not continue by treating the assumption as if it were true.
- Prove or repair the missing assumption first, compile that result, and only then resume the higher-level theorem.
- Never build an upper-level theoretical model while any part of its mathematical foundation remains unsecured; keep independent work clearly separate from blocked dependent work.
