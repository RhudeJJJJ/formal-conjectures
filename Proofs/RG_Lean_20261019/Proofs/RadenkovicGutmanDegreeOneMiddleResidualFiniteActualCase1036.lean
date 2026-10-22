/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1036 : Family 10 := level10.get ⟨1010,by decide⟩
def sourceMap1036 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1036 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1036_checked : acceptsGraphIso
    (source (graph core1036) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1971.graph sourceMap1036=true := by decide +kernel
theorem fusedMap1036_checked : acceptsGraphIso
    (fused (graph core1036) (root 10) 2 2) DegreeTwoThreeSpectrum6001.graph fusedMap1036=true := by decide +kernel
theorem certified1036 : Certified (graph core1036) (root 10) 2 2 :=
  of_native_maps core1036 DegreeOneMiddleResidualSpectrum1971.graph DegreeTwoThreeSpectrum6001.graph
    sourceMap1036 fusedMap1036 sourceMap1036_checked fusedMap1036_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1036
#print axioms sourceMap1036_checked
#print axioms fusedMap1036_checked
#print axioms certified1036
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
