# FOPPL: A First-Order Probabilistic Programming Language

This is an implementation of FOPPL, an S-expression based probabilistic
programming language described in [1]. See the `resources/examples` directory
for a list of FOPPL programs.

### Features

* Compiles FOPPL programs to a **graphical model** representation.
* Able to perform **automatic differentiation** of simple, first-order
  functions.
* Inference algorithms: **Metropolis within Gibbs** and **HMC**.
* Also supports inference of **higher-order models** using an evaluation-based
  interpreter.
* Supports the [PPX](https://github.com/probprog/ppx) protocol. This means this
  can be used as an inference engine for models written in a language without
  probabilistic constructs.

## Dependencies

* Clojure 1.8+
* Anglican 1.0+

## Usage

```
$ lein run [foppl-src]
```

[1] J. W. van de Meent, B. Paige, H. Yang, and F. Wood, “Introduction to
Probabilistic Programming,” _Foundations and Trends in Machine Learning_, pp. in
review, 2018. [arxiv.org](https://arxiv.org/abs/1809.10756)
