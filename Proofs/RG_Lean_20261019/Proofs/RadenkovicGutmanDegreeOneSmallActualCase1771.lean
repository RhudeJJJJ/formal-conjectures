/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1771 : Family 10 := level10.get ⟨4,by decide⟩
def sourceMap1771 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,12,5,6] (sourceLabel 10 0 0 v)
def fusedMap1771 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,7,0,1,2,3,4,5,6,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1771_checked : acceptsGraphIso
    (source (graph core1771) (root 10) 0 0) DegreeOneSmallSpectrum907.graph sourceMap1771=true := by decide +kernel
theorem fusedMap1771_checked : acceptsGraphIso
    (fused (graph core1771) (root 10) 0 0) DegreeOneSmallSpectrum859.graph fusedMap1771=true := by decide +kernel
theorem certified1771 : Certified (graph core1771) (root 10) 0 0 :=
  of_native_maps core1771 DegreeOneSmallSpectrum907.graph DegreeOneSmallSpectrum859.graph
    sourceMap1771 fusedMap1771 sourceMap1771_checked fusedMap1771_checked
    DegreeOneSmallComparisons.comparison1771
#print axioms sourceMap1771_checked
#print axioms fusedMap1771_checked
#print axioms certified1771
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
