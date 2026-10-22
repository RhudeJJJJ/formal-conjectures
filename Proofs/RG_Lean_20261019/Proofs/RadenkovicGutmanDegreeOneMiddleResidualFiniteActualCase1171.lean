/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1171 : Family 10 := level10.get ⟨1441,by decide⟩
def sourceMap1171 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1171 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1171_checked : acceptsGraphIso
    (source (graph core1171) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2286.graph sourceMap1171=true := by decide +kernel
theorem fusedMap1171_checked : acceptsGraphIso
    (fused (graph core1171) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1954.graph fusedMap1171=true := by decide +kernel
theorem certified1171 : Certified (graph core1171) (root 10) 2 2 :=
  of_native_maps core1171 DegreeOneMiddleResidualSpectrum2286.graph DegreeOneMiddleResidualSpectrum1954.graph
    sourceMap1171 fusedMap1171 sourceMap1171_checked fusedMap1171_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1171
#print axioms sourceMap1171_checked
#print axioms fusedMap1171_checked
#print axioms certified1171
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
