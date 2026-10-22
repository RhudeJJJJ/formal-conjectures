/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1081 : Family 10 := level10.get ⟨1115,by decide⟩
def sourceMap1081 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1081 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1081_checked : acceptsGraphIso
    (source (graph core1081) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2056.graph sourceMap1081=true := by decide +kernel
theorem fusedMap1081_checked : acceptsGraphIso
    (fused (graph core1081) (root 10) 2 2) DegreeTwoThreeSpectrum6219.graph fusedMap1081=true := by decide +kernel
theorem certified1081 : Certified (graph core1081) (root 10) 2 2 :=
  of_native_maps core1081 DegreeOneMiddleResidualSpectrum2056.graph DegreeTwoThreeSpectrum6219.graph
    sourceMap1081 fusedMap1081 sourceMap1081_checked fusedMap1081_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1081
#print axioms sourceMap1081_checked
#print axioms fusedMap1081_checked
#print axioms certified1081
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
