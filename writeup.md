# Synthesis!

## Extending the language
We first extended the language to have some bitwise operators, like `|`, `^`,
and `&`, as well as boolean negation, and bitwise inversion. We also included
comparison operators `!=`, `==`, `<`, and `>`, which mean that we can write down
some slightly more interesting examples, such as
```
x * y
x == h1 ? y : x * y
```
This synthesizes a "better" (kind of?) version of multiplication that does a
check, and maybe just returns `y` (that is, when `x == 1`). We have another
similar example with `0` instead of `y`, that will figure out the condition
`x == 0`.

We had to extend the interpreter as well, as we wanted our comparisons to return
bitvectors instead of booleans, so we have to interpret them with the Z3 "if"
expression. Other than that, the interpreter extensions were quite straightforward.
