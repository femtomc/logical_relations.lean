alias b := build

build:
  lake build

alectryon: build
  alectryon --frontend lean4+rst ProgrammingLanguageSemantics.lean -o docs/index.html --lake lakefile.lean

watch:
  find . -type f -name "ProgrammingLanguageSemantics.lean" | entr -s "just alectryon"
