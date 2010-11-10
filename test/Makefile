# PASS are tests that *should* pass.
PASS=Prelude Arithmetic Vectors typetest LetRebind Lists Trees typetest

# FAIL are tests that *should* fail.
FAIL=Append Append2 DuplicateDefinition DuplicateSignature ErrorFormatBug

UNKNOWN=bad_datatype case_bug divtest jointest langlibbug recursion-examples

TRELLYS=trellys
TYPECHECK=$(TRELLYS) -t

.PHONY: pass fail

all: pass fail

pass: $(foreach p,$(PASS),$(p).pass)

fail: $(foreach f,$(FAIL),$(f).fail)


%.pass:	%.trellys
	$(TYPECHECK) $<

%.fail: %.trellys
	! $(TYPECHECK) $<

