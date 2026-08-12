FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    latexmk \
    texlive-luatex \
    texlive-lang-japanese \
    texlive-latex-extra \
    texlive-fonts-recommended \
    texlive-bibtex-extra \
    biber \
    ghostscript \
    poppler-utils \
    make \
    git \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# The CSS/IPSJ class uses the traditional Ryumin/Gothic font names.  Embed
# IPAex fonts explicitly so the PDF does not depend on viewer-provided fonts.
RUN apt-get update && apt-get install -y --no-install-recommends \
    fonts-ipaexfont-gothic \
    fonts-ipaexfont-mincho \
    && kanji-config-updmap-sys ipaex \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /work

CMD ["latexmk", "main.tex"]
