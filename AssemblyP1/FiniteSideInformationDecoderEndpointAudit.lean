import AssemblyP1.FiniteSideInformationDecoderEndpoint

/-! Axiom audit for the #272 concrete decoder-level certainty endpoint.

Every endpoint below must depend only on the three permitted axioms
`propext`, `Classical.choice`, and `Quot.sound`. -/

#print axioms AssemblyP1.FiniteSideInformationDecoderEndpoint.fibreUnique_readStringIS_of_decoder
#print axioms AssemblyP1.FiniteSideInformationDecoderEndpoint.sufficient_readStringIS_of_decoder
#print axioms AssemblyP1.FiniteSideInformationDecoderEndpoint.weakest_readStringIS_of_decoder
#print axioms AssemblyP1.FiniteSideInformationDecoderEndpoint.conditional_certain_readStringIS_of_decoder
#print axioms AssemblyP1.FiniteSideInformationDecoderEndpoint.weakest_and_certain_readStringIS_of_decoder
