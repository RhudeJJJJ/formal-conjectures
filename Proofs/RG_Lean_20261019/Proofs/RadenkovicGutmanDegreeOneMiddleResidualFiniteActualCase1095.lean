/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1095 : Family 10 := level10.get ⟨1150,by decide⟩
def sourceMap1095 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1095 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1095_checked : acceptsGraphIso
    (source (graph core1095) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2084.graph sourceMap1095=true := by decide +kernel
theorem fusedMap1095_checked : acceptsGraphIso
    (fused (graph core1095) (root 10) 2 2) DegreeTwoThreeSpectrum6291.graph fusedMap1095=true := by decide +kernel
theorem certified1095 : Certified (graph core1095) (root 10) 2 2 :=
  of_native_maps core1095 DegreeOneMiddleResidualSpectrum2084.graph DegreeTwoThreeSpectrum6291.graph
    sourceMap1095 fusedMap1095 sourceMap1095_checked fusedMap1095_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1095
#print axioms sourceMap1095_checked
#print axioms fusedMap1095_checked
#print axioms certified1095
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
