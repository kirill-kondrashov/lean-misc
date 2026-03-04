# TaoExercises

Lean formalizations of exercises, using a project structure modeled after:
<https://github.com/kirill-kondrashov/yoccos-theorem>.

## Included formalization

- Terence Tao, *Solving mathematical problems: a personal perspective*, Exercise 2.3:
  show that `x^4 + 131 = 3y^4` has no integer solutions.

Implemented theorem:

- `TaoExercises.TaoBook.Chapter2.exercise_2_3`

## Build

```bash
lake build
lake exe check_axioms
```
