import AssemblyP1.MaximizerOrderTransform

/-! Axiom audit for the #255 fixed-x objective-equivalence lemmas.

Strictly monotone reparameterizations (e.g. log-likelihood on the
positive-support cell) share the exact-multinomial maximizer set over any
candidate set; strictly antitone maps swap max/min. Structure-independent;
settles no truth-maximality claim by itself.
-/

#print axioms AssemblyP1.MaximizerOrderTransform.isMaxOn_comp_iff
#print axioms AssemblyP1.MaximizerOrderTransform.isMinOn_comp_iff
#print axioms AssemblyP1.MaximizerOrderTransform.isMinOn_comp_iff_of_strictAnti
#print axioms AssemblyP1.MaximizerOrderTransform.isMaxOn_comp_iff_of_strictAnti
