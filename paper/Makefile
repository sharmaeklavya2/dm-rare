# This file must be run with GNU make
# Example invocations:
# make
# make COLOR=dark once

INAME = main
ONAME = dm-rare
OUT_DIR = build
TEX_OPTIONS = -cnf-line "max_print_line = 10000" -halt-on-error
ZIP_EXCLUDES = -x '.*' -x '*.db' -x '__MACOSX'

VENUE_SUFFIX = $(if $(VENUE),-$(VENUE))
BUILD_PREFIX = $(if $(OUT_DIR),$(OUT_DIR)/)
AUX_BASE = $(BUILD_PREFIX)$(ONAME)$(VENUE_SUFFIX)
INTERACTION = $(if $(SILENT),batchmode,nonstopmode)
DEFS = $(if $(COLOR),\def\colorscheme{$(COLOR)})$(if $(COMPATMODE),\def\compatmode{$(COMPATMODE)})
ISPEC = $(if $(DEFS),"$(DEFS)\input{$(INAME)$(VENUE_SUFFIX).tex}",$(INAME)$(VENUE_SUFFIX).tex)
TEX_RUN = pdflatex $(TEX_OPTIONS) -jobname=$(ONAME)$(VENUE_SUFFIX) -interaction=$(INTERACTION) $(if $(OUT_DIR),-output-directory=$(OUT_DIR) )$(ISPEC)
BIB_RUN = bibtex $(if $(SILENT),-terse )$(AUX_BASE).aux

default:
	$(if $(OUT_DIR),mkdir -p $(OUT_DIR))
	$(TEX_RUN)
	$(BIB_RUN)
	$(TEX_RUN)
	$(TEX_RUN)
	$(TEX_RUN)
once:
	$(if $(OUT_DIR),mkdir -p $(OUT_DIR))
	$(TEX_RUN)
bib:
	$(BIB_RUN)

../arxiv:
	mkdir -p ../arxiv
	cp $(AUX_BASE).bbl ../arxiv/$(ONAME)-final.bbl
	tex-flatten.py $(INAME).tex --bbl-to-link $(ONAME)-final.bbl -o ../arxiv/$(ONAME)-final.tex
	# see https://github.com/sharmaeklavya2/tex-flatten
	@echo "Now cd to arxiv and run 'pdflatex $(ONAME)-final.tex' thrice."
../arxiv.zip: ../arxiv
	cd ../arxiv && zip -r ../arxiv.zip . $(ZIP_EXCLUDES)
