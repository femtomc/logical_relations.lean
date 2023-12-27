#set page(paper: "us-letter")

= Introduction to programming language semantics in Lean 4

This is an introduction to the usage of logical relations to prove properties about languages. I'm teaching myself how this proof technique works, and I'm sharing my progress by writing code in Lean 4.

Often times we want to make statements about a language, like: "every open term in the language represents a smooth function". This is a statement which concerns the _semantics_ of the language.

== Language background

To even reach the level of being able to make these sorts of statements, we must have the background to understand language design with lambda calculus. The topics we'll start with are _syntax_, _evaluation order_, and _de Bruijn indices_.

These topics will allow us to define an `eval` function - which is a type of _operational semantics_.

=== Lambda calculus syntax
