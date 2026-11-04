setup:
    lake update
    pre-commit install

build:
    lake build --wfail

test:
    lake test

coverage *args:
    bash scripts/coverage.sh {{args}}

verify:
    lake build --wfail
    lake test
    pre-commit run --all-files
