# Coding Style

## Format

- avoid curly braces
- always add newline after `def f(...) =`
- add blank line between cases unless very compact
- introduce updated variables `x_` before constructing new objects

## Context

All code must have at all times access to context like the current script,
the current state, the current scope (type parameters + variables), etc.