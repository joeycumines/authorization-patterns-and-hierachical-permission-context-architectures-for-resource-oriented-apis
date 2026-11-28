# One extraction writes all three contracts. Grouped targets require GNU Make 4.3+.
ifeq ($(filter grouped-target,$(.FEATURES)),)
$(error GNU Make 4.3 or newer is required; use gmake on macOS)
endif

.DEFAULT_GOAL := all
.DELETE_ON_ERROR:

# Finish a requested cleanup before Make inspects the next command-line goal.
ifneq ($(filter clean,$(MAKECMDGOALS)),)
.NOTPARALLEL:
endif

NODE ?= node
PYTHON ?= python3
PROTOC ?= protoc
API_LINTER ?= api-linter
GOOGLEAPIS_DIR ?=
PROTOBUF_INCLUDE ?=
P ?=

-include config.mk

proto_dir := build/proto
contracts := authz/v1/annotations.proto authz/v1/field_guards.proto authz/v1/permission_context.proto
proto_files := $(addprefix $(proto_dir)/,$(contracts))
md_files := $(addprefix build/md/,01-overview-and-model.md 02-architecture-and-semantics.md \
    03-contracts-and-enforcement.md 04-algorithms-and-checks.md 05-version-history.md authorization-architecture-reference.md)

.PHONY: all protos check checks checks-all check-protos lint-protos browser-check export-md update-protos probe clean help

all: protos

protos: $(proto_files)

$(proto_files) &: index.html hack/extract-protos.py Makefile
	"$(PYTHON)" hack/extract-protos.py $< $(proto_dir) $(contracts)

check: checks check-protos lint-protos browser-check verify-formal

checks:
	"$(NODE)" hack/run-checks.js index.html

# record-formal runs the same proof, parity and mutation checks before writing
# digests for a reviewed specification or formalization change.
.PHONY: verify-formal record-formal
verify-formal:
	"$(NODE)" hack/formal/verify.js

record-formal:
	"$(NODE)" hack/formal/verify.js --record

checks-all:
	"$(NODE)" hack/run-checks.js index.html --all

check-protos: protos
	diff -ru proto $(proto_dir)

export PROTOC API_LINTER GOOGLEAPIS_DIR PROTOBUF_INCLUDE
lint-protos: protos
	$(SHELL) hack/lint-protos.sh $(proto_dir) $(contracts)

update-protos: protos
	@set -e; for file in $(contracts); do \
	  mkdir -p "proto/$${file%/*}"; \
	  cmp -s "$(proto_dir)/$$file" "proto/$$file" || cp "$(proto_dir)/$$file" "proto/$$file"; \
	done

browser-check:
	"$(NODE)" hack/browser-check.js

export-md:
	"$(NODE)" hack/export-md.js

export P
probe:
	@case "$$P" in ''|*[!a-zA-Z0-9_-]*) echo 'Usage: make probe P=<name from hack/probes>' >&2; exit 2;; esac; \
	test -f "hack/probes/$$P.js" || { echo "Unknown probe: $$P" >&2; exit 2; }; \
	"$(NODE)" "hack/probes/$$P.js" index.html

clean:
	$(RM) $(proto_files) $(md_files)
	@rmdir $(proto_dir)/authz/v1 $(proto_dir)/authz $(proto_dir) build/md build 2>/dev/null || :

help:
	@printf '%s\n' \
	  'all (default)  Extract the published protobuf contracts into ./build/proto/' \
	  'check          Run the model, protobuf, browser and Lean checks' \
	  'checks         Run the model checks (checks-all prints every result)' \
	  'verify-formal   Audit Lean proofs and compare the compiled oracle with the HTML' \
	  'record-formal   Reverify and record the reviewed hashes in the manifest' \
	  'check-protos   Compare the extracted contracts with ./proto/' \
	  'lint-protos    Compile and lint the extracted contracts' \
	  'browser-check  Exercise the local specification in headless Chrome' \
	  'export-md      Write the six Markdown documents to ./build/md/' \
	  'update-protos  Refresh the checked-in copies after a contract change' \
	  'probe P=name   Run a named diagnostic from ./hack/probes/' \
	  'clean          Remove the generated contracts and Markdown exports'
