ROOT=~/data
INCOMING=~/data/unproc
DIEBOLD_ROOT=~/tevs/tevs/diebold_data
DIEBOLD_INCOMING=~/tevs/tevs/diebold_data/unproc
VANCOUVER_ROOT=~/tevs/tevs/vancouver_data
VANCOUVER_INCOMING=~/tevs/tevs/vancouver_data/unproc
DOCS=~/tevs-docs

all: reset run docs

run: reset
	@./main.py

reset: clean
	@cp -r ${ROOT}/proc/* ${INCOMING} 2>/dev/null || true
	@rm -rf ${ROOT}/proc/*
	@rm -rf ${ROOT}/errors/*
	@rm -rf ${ROOT}/results/*
	@cat ${ROOT}/log.txt >>${ROOT}/log.old 2>/dev/null || true
	@rm -f ${ROOT}/log.txt
	@echo 1 >${ROOT}/nexttoprocess.txt
	@cp -r ${DIEBOLD_ROOT}/proc/* ${DIEBOLD_INCOMING} 2>/dev/null || true
	@rm -rf ${DIEBOLD_ROOT}/proc/*
	@rm -rf ${DIEBOLD_ROOT}/errors/*
	@rm -rf ${DIEBOLD_ROOT}/results/*
	@cat ${DIEBOLD_ROOT}/log.txt >>${DIEBOLD_ROOT}/log.old 2>/dev/null || true
	@rm -f ${DIEBOLD_ROOT}/log.txt
	@echo 1 >${DIEBOLD_ROOT}/nexttoprocess.txt
	@cp -r ${VANCOUVER_ROOT}/proc/* ${VANCOUVER_INCOMING} 2>/dev/null || true
	@rm -rf ${VANCOUVER_ROOT}/proc/*
	@rm -rf ${VANCOUVER_ROOT}/errors/*
	@rm -rf ${VANCOUVER_ROOT}/results/*
	@cat ${VANCOUVER_ROOT}/log.txt >>${VANCOUVER_ROOT}/log.old 2>/dev/null || true
	@rm -f ${VANCOUVER_ROOT}/log.txt
	@echo 1 >${VANCOUVER_ROOT}/nexttoprocess.txt

reset-templates: reset
	@rm -rf ${ROOT}/templates/*
	@rm -rf ${ROOT}/template_images/*
	@rm -rf ${ROOT}/composite_images/*
	@rm -rf ${DIEBOLD_ROOT}/templates/*
	@rm -rf ${DIEBOLD_ROOT}/template_images/*
	@rm -rf ${DIEBOLD_ROOT}/composite_images/*
	@rm -rf ${VANCOUVER_ROOT}/templates/*
	@rm -rf ${VANCOUVER_ROOT}/template_images/*
	@rm -rf ${VANCOUVER_ROOT}/composite_images/*

reset-db: reset reset-templates
	@echo "delete from voteops; delete from ballots" | psql >/dev/null

clean:
	@rm -f *.pyc

docs:
	@PYTHONPATH=$PYTHONPATH:. sphinx-build -b html -aqE docs docs/sphinx
	@cd docs && ./mkug.sh

test: *.py
	@nosetests -q --with-doctest #--with-coverage --cover-erase --cover-html --cover-html-dir=coverage

.PHONY: docs clean reset reset-templates
