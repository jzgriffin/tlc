PDFLATEX ?= pdflatex

.PHONY: all clean distclean
all: all-report
clean: clean-report
distclean: distclean-report

report.OUTPUT := report.pdf
report.SOURCE := report.tex
report.OBJECT := \
    report.aux \
    report.log
.PHONY: all-report clean-report distclean-report
all-report: $(report.OUTPUT)
clean-report:
	$(RM) $(report.OBJECT)
distclean-report: clean-report
	$(RM) $(report.OUTPUT)
$(report.OUTPUT): $(report.SOURCE)
	$(PDFLATEX) $(PDFLATEXFLAGS) $?
