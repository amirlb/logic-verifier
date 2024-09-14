# ☀️ Sol theorem prover

Sol is a proof assistant with ambitious goals: to automate proving large
swaths of mathematical literature, and help uncover interesting structures
and definitions.

Is it currently in an early stage of this long-term plan.

## Why a new proof assistant?

Sol is based on second-order predicate logic.

This is not common. Most if not all of the proof assistants implemented in
the last 40 years were based on type theory. This encourages some concepts
that are a bit foreign to mathematicians, such as having all functions be
total, which doesn't make sense, e.g. for the inversion operation in fields.
In addition the use of type theory stems from computer-science bias, leading
to the natural way of writing proofs being program-like. Programs are even
harder to read than mathematical proofs, and it requires effort to organize
the proof into mathematical-looking language.

Mizar is an exception and an inspiration for this project. It supports a
community with a large mathematical library, composed over decades. The code
base however is complicated and it might be easier to implement a new prover
if the focus is different. Part of the Sol project is re-verifying the Mizar
Mathematical Library.

## The logic of Sol

The core language of Sol is second-order predicate logic, without constants
or function symbols. Variables are an abstract type, which are introduced by
binding functions. This means that only closed formulas can be created.

Proofs are implicit and not recorded. There are constructors that generate
judgements `A₁, ..., Aₙ ⊢ B` from formulas and from other judgements. The
constructors closely imitate the inference rules of natural deductions. Two
main differences are
1. There are no specific introduction and elimination rules for logical
    connectives, instead a SAT solver creates pattern-based inference rules
    for any template with connectives. The use of a SAT solver makes the
    logic classical, as it can create the inference rule `¬¬P ⊢ P`.
2. Eliminating second-order universal quantification replaces the bound
    predicate symbol with any open formula with the same signature. This
    has the same power as the axiom of comprehension in other formulations
    of second-order logic.

Constant predicate symbols can be defined by the user and are used to encode
the basic predicate of the language. The main part of the library is based
on set theory and defines two predicate symbols for equality and for set
membership.

Most predicates are defined as shorthands, which the core logic implements
efficiently. Functions are defined after proving existence and uniqueness
for all inputs and are translated to predicates in the core language.
