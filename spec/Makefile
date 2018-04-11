# This makefile supports building a spec alone, or the full paper

## Shared variables
RULESFILE = ett-rules.tex

## For spec alone
SPEC      = ett.ott
SPECFILE  = spec.tex

## For paper
OTT_SOURCE = ett
OTT_LOC    = ~/github/roles/corespec/spec

OTTFILES  = $(foreach i, $(OTT_SOURCE), $(OTT_LOC)/$(i).ott)
OTTIFLAGS = $(foreach i, $(OTT_SOURCE), -i $(OTT_LOC)/$(i).ott)
RULESFILE = ett-rules.tex

TOP=paper
PDFS=paper.pdf spec.pdf



all: spec
paper: $(TOP).pdf

%.tex: $(RULESFILE) %.mng Makefile
	ott $(OTTIFLAGS) \
										-tex_wrap false \
										-tex_show_meta false \
										-tex_filter $*.mng $*.tex

ett-rules.tex: $(OTTFILES)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
					-tex_wrap false \
					-tex_show_meta false

%.pdf : paper.tex
	latexmk -bibtex -pdf paper.tex

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~ *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out

clean: paperclean


spec: $(SPEC)
	ott -o $(RULESFILE) \
					-tex_wrap false \
					-tex_show_meta false $(SPEC)
	pdflatex -interaction nonstopmode $(SPECFILE)


spec-continuous-update: $(SPEC)
	# Only caveat: it doesn't register saves that happen while recompiling
	# Have to use an ulgy sed as Ott's -colour option is broken
	while inotifywait -qe close_write $(SPEC); do                   \
		(                                                             \
			ott -o $(RULESFILE)                                         \
					-colour false                                           \
					-tex_wrap false                                         \
					-tex_show_meta false                                    \
					$(SPEC)                                                 \
					2>&1                                                    \
					| sed -r "s/\x1B\[([0-9]{1,2}(;[0-9]{1,2})?)?[mGK]//g"; \
			echo "\n\n";                                                \
			pdflatex                                                    \
			    -interaction nonstopmode                                \
			    $(SPECFILE)                                             \
					-file-line-error                                        \
					2>&1;                                                   \
		) | fold -w 80 | column -e;                                   \
		echo "\n";                                                    \
		done
