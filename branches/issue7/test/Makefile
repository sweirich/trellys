# main rules
# ==========
#
# make [all]: does a regression test, by checking that everything that
#             was correctly passing (failing) type checking is still
#             passing (failing) type checking.  Prints *nothing* on
#             success.
#
# make todo: tests if known-broken things are still broken.  If you
#            fix something in TODO_PASS (TODO_FAIL) than move it to
#            PASS (FAIL).  NB: nothing is printed for fixed items
#            ... this is probably confusing.

# PASS are tests that *should* always pass.
PASS=Prelude Arithmetic Vectors typetest LetRebind Lists Trees typetest Append2
# FAIL are tests that *should* always fail.
FAIL=Append  DuplicateDefinition DuplicateSignature ErrorFormatBug
# TODO_FAIL are tests that *should* fail but currently pass.
TODO_FAIL=SigDefBug
# TODO_PASS are tests that *should* pass but currently fail.
TODO_PASS=
# stale?
UNKNOWN=bad_datatype case_bug divtest jointest langlibbug recursion-examples

TRELLYS=trellys
# typecheck *quietly*
TYPECHECK=$(TRELLYS) -t 1>/dev/null 2>&1

.PHONY: pass fail todo_pass todo_fail todo

all: pass fail

pass: $(foreach p,$(PASS),$(p).pass)
fail: $(foreach f,$(FAIL),$(f).fail)
todo_pass: $(foreach f,$(TODO_PASS),$(f).pass)
todo_fail: $(foreach f,$(TODO_FAIL),$(f).fail) 
todo: todo_pass todo_fail

%.pass:	%.trellys
	@  $(TYPECHECK) $< || echo "$< failed (should pass)" >&2

%.fail: %.trellys
	@! $(TYPECHECK) $< || echo "$< passed (should fail)" >&2
