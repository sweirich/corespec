SPEC      = ett.ott
RULESFILE = ett-rules.tex
SPECFILE  = spec.tex

all: $(SPEC) $(SPECTEX)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false $(SPEC)
	pdflatex $(SPECFILE)
