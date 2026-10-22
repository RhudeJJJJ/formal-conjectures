/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1195 : Family 10 := level10.get ⟨1626,by decide⟩
def sourceMap1195 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1195 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1195_checked : acceptsGraphIso
    (source (graph core1195) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2351.graph sourceMap1195=true := by decide +kernel
theorem fusedMap1195_checked : acceptsGraphIso
    (fused (graph core1195) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1603.graph fusedMap1195=true := by decide +kernel
theorem certified1195 : Certified (graph core1195) (root 10) 2 2 :=
  of_native_maps core1195 DegreeOneMiddleResidualSpectrum2351.graph DegreeOneMiddleResidualSpectrum1603.graph
    sourceMap1195 fusedMap1195 sourceMap1195_checked fusedMap1195_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1195
#print axioms sourceMap1195_checked
#print axioms fusedMap1195_checked
#print axioms certified1195
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
