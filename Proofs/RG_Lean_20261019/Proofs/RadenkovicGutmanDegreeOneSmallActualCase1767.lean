/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1767 : Family 10 := level10.get ⟨0,by decide⟩
def sourceMap1767 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (sourceLabel 10 0 0 v)
def fusedMap1767 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap1767_checked : acceptsGraphIso
    (source (graph core1767) (root 10) 0 0) DegreeOneSmallSpectrum856.graph sourceMap1767=true := by decide +kernel
theorem fusedMap1767_checked : acceptsGraphIso
    (fused (graph core1767) (root 10) 0 0) DegreeOneSmallSpectrum861.graph fusedMap1767=true := by decide +kernel
theorem certified1767 : Certified (graph core1767) (root 10) 0 0 :=
  of_native_maps core1767 DegreeOneSmallSpectrum856.graph DegreeOneSmallSpectrum861.graph
    sourceMap1767 fusedMap1767 sourceMap1767_checked fusedMap1767_checked
    DegreeOneSmallComparisons.comparison1767
#print axioms sourceMap1767_checked
#print axioms fusedMap1767_checked
#print axioms certified1767
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
