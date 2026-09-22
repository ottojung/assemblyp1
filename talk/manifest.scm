;; Minimal TeX environment for the AssemblyP1 talk.
;; From talk/: guix shell -m manifest.scm -- latexmk -pdf main.tex
(specifications->manifest
 '("texlive-scheme-basic"
   "texlive-latexmk"
   "texlive-amsmath"
   "texlive-hyperref"
   "texlive-xcolor"
   "texlive-pgf"
   "texlive-beamer"
   "texlive-lm"))
