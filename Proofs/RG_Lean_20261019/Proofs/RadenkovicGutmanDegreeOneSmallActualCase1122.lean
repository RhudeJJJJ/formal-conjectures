/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1122 : Family 8 := level8.get ⟨164,by decide⟩
def sourceMap1122 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1122 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1122_checked : acceptsGraphIso
    (source (graph core1122) (root 8) 1 1) DegreeOneSmallSpectrum1928.graph sourceMap1122=true := by decide +kernel
theorem fusedMap1122_checked : acceptsGraphIso
    (fused (graph core1122) (root 8) 1 1) DegreeOneSmallSpectrum1471.graph fusedMap1122=true := by decide +kernel
theorem certified1122 : Certified (graph core1122) (root 8) 1 1 :=
  of_native_maps core1122 DegreeOneSmallSpectrum1928.graph DegreeOneSmallSpectrum1471.graph
    sourceMap1122 fusedMap1122 sourceMap1122_checked fusedMap1122_checked
    DegreeOneSmallComparisons.comparison1122
#print axioms sourceMap1122_checked
#print axioms fusedMap1122_checked
#print axioms certified1122
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
