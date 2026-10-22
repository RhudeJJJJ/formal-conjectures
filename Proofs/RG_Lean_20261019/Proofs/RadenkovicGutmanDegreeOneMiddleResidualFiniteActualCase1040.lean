/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1040 : Family 10 := level10.get ⟨1016,by decide⟩
def sourceMap1040 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1040 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1040_checked : acceptsGraphIso
    (source (graph core1040) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1977.graph sourceMap1040=true := by decide +kernel
theorem fusedMap1040_checked : acceptsGraphIso
    (fused (graph core1040) (root 10) 2 2) DegreeTwoThreeSpectrum6014.graph fusedMap1040=true := by decide +kernel
theorem certified1040 : Certified (graph core1040) (root 10) 2 2 :=
  of_native_maps core1040 DegreeOneMiddleResidualSpectrum1977.graph DegreeTwoThreeSpectrum6014.graph
    sourceMap1040 fusedMap1040 sourceMap1040_checked fusedMap1040_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1040
#print axioms sourceMap1040_checked
#print axioms fusedMap1040_checked
#print axioms certified1040
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
