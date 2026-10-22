/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1101 : Family 10 := level10.get ⟨1177,by decide⟩
def sourceMap1101 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1101 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1101_checked : acceptsGraphIso
    (source (graph core1101) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2102.graph sourceMap1101=true := by decide +kernel
theorem fusedMap1101_checked : acceptsGraphIso
    (fused (graph core1101) (root 10) 2 2) DegreeTwoThreeSpectrum6340.graph fusedMap1101=true := by decide +kernel
theorem certified1101 : Certified (graph core1101) (root 10) 2 2 :=
  of_native_maps core1101 DegreeOneMiddleResidualSpectrum2102.graph DegreeTwoThreeSpectrum6340.graph
    sourceMap1101 fusedMap1101 sourceMap1101_checked fusedMap1101_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1101
#print axioms sourceMap1101_checked
#print axioms fusedMap1101_checked
#print axioms certified1101
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
