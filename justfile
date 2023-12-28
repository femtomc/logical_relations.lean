alias b := build

build:
  lake build

alectryon: build
  alectryon --frontend lean4 ProgrammingLanguageSemantics.lean -o docs/index.html --lake lakefile.lean
