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
PASS=Prelude Arithmetic Vectors LetRebind Trees Append2 TypeTest NatElimination \
     CastShiftTrick ErasedConv Test_Q_Cons StrongNat LessThanNat \
     LessThanNat_LT LessThanNat_lt_eq_True ProgrammaticCdiv \
     TerminationAsValueRestrictionWorkaround Subvert \
     BasicOrd
# TODO_FAIL are tests that *should* fail but currently pass.
TODO_FAIL=
# TODO_PASS are tests that *should* pass but currently fail.
TODO_PASS=ProgList
# stale?
UNKNOWN= case_bug divtest jointest langlibbug recursion-examples
# A symlink to the ../.capri local trellys, installed by top level make.
TRELLYS=./trellys
# typecheck *quietly*
TYPECHECK=$(TRELLYS) -e 1>/dev/null # 2>&1

.PHONY: pass fail todo_pass todo_fail todo

all: pass fail

clean:
	rm *.trellys-elaborated

pass: $(foreach p,$(PASS),$(p).pass)

# FAIL are tests that *should* always fail.
FAIL=Append \
     Test_T_RN2_FV

fail:
	@./expect_error FreeVarsBug "variable n appears free in body"
	@./expect_error DuplicateDefinition "Multiple definitions of"
	@./expect_error DuplicateSignature "Duplicate type signature"
	@./expect_error SigDefBug "The variable p was not found"
	@./expect_error bad_datatype "occurs in non-positive position"
	@./expect_error ErasedConvBad "is marked erased"
	@./expect_error Test_T_Let_1_FV "appear in the erasure of the body"
	@./expect_error Test_T_Let_2_FV_1 "appear in the erasure of the body"
	@./expect_error Test_T_Let_2_FV_2 "appear in the erasure of the body"
	@./expect_error Test_T_Rec2_FV "variable n appears free in body"
	@./expect_error Bug_T_Case_FV "should not appear in the erasure"
	@./expect_error Test_T_RN2_FV "variable n appears free in body"

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
