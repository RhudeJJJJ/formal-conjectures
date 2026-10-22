/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1136 : Family 10 := level10.get ⟨1301,by decide⟩
def sourceMap1136 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1136 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1136_checked : acceptsGraphIso
    (source (graph core1136) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2189.graph sourceMap1136=true := by decide +kernel
theorem fusedMap1136_checked : acceptsGraphIso
    (fused (graph core1136) (root 10) 2 2) DegreeTwoThreeSpectrum6590.graph fusedMap1136=true := by decide +kernel
theorem certified1136 : Certified (graph core1136) (root 10) 2 2 :=
  of_native_maps core1136 DegreeOneMiddleResidualSpectrum2189.graph DegreeTwoThreeSpectrum6590.graph
    sourceMap1136 fusedMap1136 sourceMap1136_checked fusedMap1136_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1136
#print axioms sourceMap1136_checked
#print axioms fusedMap1136_checked
#print axioms certified1136
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
