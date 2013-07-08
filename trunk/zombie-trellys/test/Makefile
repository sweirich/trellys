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
PASS=Prelude Arithmetic Arithmetic-old Vectors Product List Fin LetRebind Trees Append2 \
     Append2-old AppendUni TypeTest NatElimination \
     CastShiftTrick ErasedConv ErasedConvInfer Test_Q_Cons StrongNat LessThanNat \
     LessThanNat_LT LessThanNat_lt_eq_True ProgrammaticCdiv Divtest \
     TerminationAsValueRestrictionWorkaround Subvert \
     BasicOrd DeepMatch CongruenceTests UnfoldTests \
     RLE BST

# TODO_FAIL are tests that *should* fail but currently pass.
TODO_FAIL=
# TODO_PASS are tests that *should* pass but currently fail.
TODO_PASS=ProgList
# stale?
UNKNOWN=  recursion-examples Append
# A symlink to the ../.capri local trellys, installed by top level make.
TRELLYS=./trellys 
# typecheck *quietly*
TYPECHECK=$(TRELLYS) 1>/dev/null # 2>&1

.PHONY: pass fail todo_pass todo_fail todo

all: pass fail

clean:
	rm *.trellys-elaborated

pass: $(foreach p,$(PASS),$(p).pass)

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
	@./expect_error Bug_T_Case_FV "should not appear in the erasure of the case expression"
	@./expect_error Bug_T_Case_FV_2 "should not appear in the erasure of the case expression"
	@./expect_error Test_T_RN2_FV "variable n appears free in body"
	@./expect_error jointest "The erasures of terms .* are not joinable."
	@./expect_error DeepMatchError1 "must be a member of a datatype, but is not."
	@./expect_error DeepMatchError2 "is a member of an abstract datatype"
	@./expect_error DeepMatchError3 "should take 1 constructors,"
	@./expect_error DeepMatchError4 "wrong epsilons on arguments in pattern"
	@./expect_error DeepMatchError5 "Each branch should have 2 patterns, but"
	@./expect_error DeepMatchNonExhaustive1 "Patterns in case-expression not exhaustive."
	@./expect_error DeepMatchNonExhaustive2 "Patterns in case-expression not exhaustive."

extraction: $(foreach p,$(PASS),$(p).extraction) 

todo_pass: $(foreach f,$(TODO_PASS),$(f).pass)
todo_fail: $(foreach f,$(TODO_FAIL),$(f).fail)
todo: todo_pass todo_fail
	@echo
	@echo "Any names printed *without* errors should be moved from TODO_* to *"

%.pass:	%.trellys
	@echo -n "$<: "
	@if ! $(TYPECHECK) $<; then echo -e "\033[1;31mfailed\033[0;30m (should pass)" >&2; else echo; fi

%.extraction:	%.trellys
	@echo -n "$< (testing extraction)"
	@if ! ($(TYPECHECK) --extraction $< && ocamlc -w -A $*.ml); then echo -e "\033[1;31mfailed\033[0;30m (should pass)" >&2; else echo; fi


%.fail: %.trellys
	@echo -n "$<: "
	@if $(TYPECHECK) $<; then echo -e "\033[1;31mpassed\033[0;30m (should fail)" >&2; else echo; fi
