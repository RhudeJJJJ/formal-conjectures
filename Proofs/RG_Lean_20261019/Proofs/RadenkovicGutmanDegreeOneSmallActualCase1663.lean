/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1663 : Family 9 := level9.get ⟨421,by decide⟩
def sourceMap1663 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (sourceLabel 9 0 0 v)
def fusedMap1663 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1663_checked : acceptsGraphIso
    (source (graph core1663) (root 9) 0 0) DegreeOneSmallSpectrum702.graph sourceMap1663=true := by decide +kernel
theorem fusedMap1663_checked : acceptsGraphIso
    (fused (graph core1663) (root 9) 0 0) DegreeOneSmallSpectrum786.graph fusedMap1663=true := by decide +kernel
theorem certified1663 : Certified (graph core1663) (root 9) 0 0 :=
  of_native_maps core1663 DegreeOneSmallSpectrum702.graph DegreeOneSmallSpectrum786.graph
    sourceMap1663 fusedMap1663 sourceMap1663_checked fusedMap1663_checked
    DegreeOneSmallComparisons.comparison1663
#print axioms sourceMap1663_checked
#print axioms fusedMap1663_checked
#print axioms certified1663
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
