/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1435 : Family 9 := level9.get ⟨174,by decide⟩
def sourceMap1435 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1435 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1435_checked : acceptsGraphIso
    (source (graph core1435) (root 9) 0 0) DegreeOneSmallSpectrum745.graph sourceMap1435=true := by decide +kernel
theorem fusedMap1435_checked : acceptsGraphIso
    (fused (graph core1435) (root 9) 0 0) DegreeOneSmallSpectrum458.graph fusedMap1435=true := by decide +kernel
theorem certified1435 : Certified (graph core1435) (root 9) 0 0 :=
  of_native_maps core1435 DegreeOneSmallSpectrum745.graph DegreeOneSmallSpectrum458.graph
    sourceMap1435 fusedMap1435 sourceMap1435_checked fusedMap1435_checked
    DegreeOneSmallComparisons.comparison1435
#print axioms sourceMap1435_checked
#print axioms fusedMap1435_checked
#print axioms certified1435
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
