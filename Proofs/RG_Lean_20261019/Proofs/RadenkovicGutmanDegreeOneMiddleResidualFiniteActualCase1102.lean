/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1102 : Family 10 := level10.get ⟨1178,by decide⟩
def sourceMap1102 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1102 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1102_checked : acceptsGraphIso
    (source (graph core1102) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2103.graph sourceMap1102=true := by decide +kernel
theorem fusedMap1102_checked : acceptsGraphIso
    (fused (graph core1102) (root 10) 2 2) DegreeTwoThreeSpectrum6343.graph fusedMap1102=true := by decide +kernel
theorem certified1102 : Certified (graph core1102) (root 10) 2 2 :=
  of_native_maps core1102 DegreeOneMiddleResidualSpectrum2103.graph DegreeTwoThreeSpectrum6343.graph
    sourceMap1102 fusedMap1102 sourceMap1102_checked fusedMap1102_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1102
#print axioms sourceMap1102_checked
#print axioms fusedMap1102_checked
#print axioms certified1102
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
