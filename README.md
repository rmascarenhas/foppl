# FOPPL: A First-Order Probabilistic Programming Language

This is an implementation of FOPPL, as described in [1]. Compiles programs
to a graphical model representation. See `src/foppl/operations.clj` for the list
of functions available on the resulting graphical model data structure.

## Dependencies

* Clojure 1.8+
* Anglican 1.0+

## Usage

```
$ lein run [foppl-src]
```

By default, compiling a valid FOPPL program as above will print the resulting graphical
model to the screen (using the `print-graph` function).


[1] J. W. van de Meent, B. Paige, H. Yang, and F. Wood, “Introduction to
Probabilistic Programming,” _Foundations and Trends in Machine Learning_, pp. in
review, 2018.
