# Main Rules
# ==========
#
# make [all]: does a regression test, by checking that everything that
#             was correctly passing (failing) type checking is still
#             passing (failing) type checking.
#
# make todo: tests if known-broken things are still broken.  If you
#            fix something in TODO_PASS (TODO_FAIL) then you should
#            move it to PASS (FAIL).

# Use bash to run targets.
SHELL=/bin/bash

# PASS are tests that *should* always pass.
PASS=Prelude Arithmetic Vectors LetRebind Lists Trees Append2 typetest NatElimination Ott \
     OttAppend CastShiftTrick ErasedConv ProgList Test_Q_Cons
# FAIL are tests that *should* always fail.
FAIL=Append  DuplicateDefinition DuplicateSignature ErrorFormatBug SigDefBug\
     bad_datatype ErasedConvBad Test_T_Let_2_FV_1 Test_T_Rec2_FV Test_T_Let_1_FV\
     Test_T_Let_2_FV_2  Test_T_RN2_FV FreeVarsBug
# TODO_FAIL are tests that *should* fail but currently pass.
TODO_FAIL=
# TODO_PASS are tests that *should* pass but currently fail.
TODO_PASS=
# stale?
UNKNOWN= case_bug divtest jointest langlibbug recursion-examples
# A symlink to the ../.capri local trellys, installed by top level make.
TRELLYS=./trellys
# typecheck *quietly*
TYPECHECK=$(TRELLYS) -te 1>/dev/null 2>&1

.PHONY: pass fail todo_pass todo_fail todo

all: pass fail

clean:
	rm *.trellys-elaborated

pass: $(foreach p,$(PASS),$(p).pass)
fail: $(foreach f,$(FAIL),$(f).fail)
todo_pass: $(foreach f,$(TODO_PASS),$(f).pass)
todo_fail: $(foreach f,$(TODO_FAIL),$(f).fail)
todo: todo_pass todo_fail
	@echo
	@echo "Any names printed *without* errors should be moved from TODO_* to *"

%.pass:	%.trellys
	@echo -n "$<: "
	@if ! $(TYPECHECK) $<; then echo "failed (should pass)" >&2; else echo; fi

%.fail: %.trellys
	@echo -n "$<: "
	@if $(TYPECHECK) $<; then echo "passed (should fail)" >&2; else echo; fi
