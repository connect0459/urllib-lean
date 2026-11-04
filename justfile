setup:
    lake update
    pre-commit install

build:
    lake build --wfail

test:
    lake test

verify:
    lake build --wfail
    lake test
    pre-commit run --all-files
