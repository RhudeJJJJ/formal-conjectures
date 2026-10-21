/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1555 : Family 9 := level9.get ⟨288,by decide⟩
def sourceMap1555 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,8,9,10,11,1,2,3,4,6,7] (sourceLabel 9 0 0 v)
def fusedMap1555 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,8,9,10,11,1,2,3,4,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1555_checked : acceptsGraphIso
    (source (graph core1555) (root 9) 0 0) DegreeOneSmallSpectrum459.graph sourceMap1555=true := by decide +kernel
theorem fusedMap1555_checked : acceptsGraphIso
    (fused (graph core1555) (root 9) 0 0) DegreeOneSmallSpectrum458.graph fusedMap1555=true := by decide +kernel
theorem certified1555 : Certified (graph core1555) (root 9) 0 0 :=
  of_native_maps core1555 DegreeOneSmallSpectrum459.graph DegreeOneSmallSpectrum458.graph
    sourceMap1555 fusedMap1555 sourceMap1555_checked fusedMap1555_checked
    DegreeOneSmallComparisons.comparison1555
#print axioms sourceMap1555_checked
#print axioms fusedMap1555_checked
#print axioms certified1555
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
