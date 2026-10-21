/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1774 : Family 10 := level10.get ⟨7,by decide⟩
def sourceMap1774 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,8,9,10,11,12,7,5,6] (sourceLabel 10 0 0 v)
def fusedMap1774 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1774_checked : acceptsGraphIso
    (source (graph core1774) (root 10) 0 0) DegreeOneSmallSpectrum887.graph sourceMap1774=true := by decide +kernel
theorem fusedMap1774_checked : acceptsGraphIso
    (fused (graph core1774) (root 10) 0 0) DegreeOneSmallSpectrum859.graph fusedMap1774=true := by decide +kernel
theorem certified1774 : Certified (graph core1774) (root 10) 0 0 :=
  of_native_maps core1774 DegreeOneSmallSpectrum887.graph DegreeOneSmallSpectrum859.graph
    sourceMap1774 fusedMap1774 sourceMap1774_checked fusedMap1774_checked
    DegreeOneSmallComparisons.comparison1774
#print axioms sourceMap1774_checked
#print axioms fusedMap1774_checked
#print axioms certified1774
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
