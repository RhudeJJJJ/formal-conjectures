/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1143 : Family 10 := level10.get ⟨1320,by decide⟩
def sourceMap1143 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1143 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1143_checked : acceptsGraphIso
    (source (graph core1143) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2204.graph sourceMap1143=true := by decide +kernel
theorem fusedMap1143_checked : acceptsGraphIso
    (fused (graph core1143) (root 10) 2 2) DegreeTwoThreeSpectrum6629.graph fusedMap1143=true := by decide +kernel
theorem certified1143 : Certified (graph core1143) (root 10) 2 2 :=
  of_native_maps core1143 DegreeOneMiddleResidualSpectrum2204.graph DegreeTwoThreeSpectrum6629.graph
    sourceMap1143 fusedMap1143 sourceMap1143_checked fusedMap1143_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1143
#print axioms sourceMap1143_checked
#print axioms fusedMap1143_checked
#print axioms certified1143
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
