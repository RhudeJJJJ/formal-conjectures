/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1770 : Family 10 := level10.get ⟨3,by decide⟩
def sourceMap1770 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (sourceLabel 10 0 0 v)
def fusedMap1770 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1770_checked : acceptsGraphIso
    (source (graph core1770) (root 10) 0 0) DegreeOneSmallSpectrum904.graph sourceMap1770=true := by decide +kernel
theorem fusedMap1770_checked : acceptsGraphIso
    (fused (graph core1770) (root 10) 0 0) DegreeOneSmallSpectrum858.graph fusedMap1770=true := by decide +kernel
theorem certified1770 : Certified (graph core1770) (root 10) 0 0 :=
  of_native_maps core1770 DegreeOneSmallSpectrum904.graph DegreeOneSmallSpectrum858.graph
    sourceMap1770 fusedMap1770 sourceMap1770_checked fusedMap1770_checked
    DegreeOneSmallComparisons.comparison1770
#print axioms sourceMap1770_checked
#print axioms fusedMap1770_checked
#print axioms certified1770
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
