/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1377 : Family 9 := level9.get ⟨125,by decide⟩
def sourceMap1377 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,1,0,8,9,10,11,2,3,4,6,7] (sourceLabel 9 0 0 v)
def fusedMap1377 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1377_checked : acceptsGraphIso
    (source (graph core1377) (root 9) 0 0) DegreeOneSmallSpectrum567.graph sourceMap1377=true := by decide +kernel
theorem fusedMap1377_checked : acceptsGraphIso
    (fused (graph core1377) (root 9) 0 0) DegreeOneSmallSpectrum563.graph fusedMap1377=true := by decide +kernel
theorem certified1377 : Certified (graph core1377) (root 9) 0 0 :=
  of_native_maps core1377 DegreeOneSmallSpectrum567.graph DegreeOneSmallSpectrum563.graph
    sourceMap1377 fusedMap1377 sourceMap1377_checked fusedMap1377_checked
    DegreeOneSmallComparisons.comparison1377
#print axioms sourceMap1377_checked
#print axioms fusedMap1377_checked
#print axioms certified1377
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
