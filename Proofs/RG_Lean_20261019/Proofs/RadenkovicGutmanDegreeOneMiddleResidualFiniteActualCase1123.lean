/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1123 : Family 10 := level10.get ⟨1258,by decide⟩
def sourceMap1123 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1123 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1123_checked : acceptsGraphIso
    (source (graph core1123) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2158.graph sourceMap1123=true := by decide +kernel
theorem fusedMap1123_checked : acceptsGraphIso
    (fused (graph core1123) (root 10) 2 2) DegreeTwoThreeSpectrum6508.graph fusedMap1123=true := by decide +kernel
theorem certified1123 : Certified (graph core1123) (root 10) 2 2 :=
  of_native_maps core1123 DegreeOneMiddleResidualSpectrum2158.graph DegreeTwoThreeSpectrum6508.graph
    sourceMap1123 fusedMap1123 sourceMap1123_checked fusedMap1123_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1123
#print axioms sourceMap1123_checked
#print axioms fusedMap1123_checked
#print axioms certified1123
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
