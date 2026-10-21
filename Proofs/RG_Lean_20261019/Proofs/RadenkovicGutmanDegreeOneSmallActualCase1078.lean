/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1078 : Family 8 := level8.get ⟨137,by decide⟩
def sourceMap1078 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1078 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1078_checked : acceptsGraphIso
    (source (graph core1078) (root 8) 1 1) DegreeOneSmallSpectrum1916.graph sourceMap1078=true := by decide +kernel
theorem fusedMap1078_checked : acceptsGraphIso
    (fused (graph core1078) (root 8) 1 1) DegreeOneSmallSpectrum1323.graph fusedMap1078=true := by decide +kernel
theorem certified1078 : Certified (graph core1078) (root 8) 1 1 :=
  of_native_maps core1078 DegreeOneSmallSpectrum1916.graph DegreeOneSmallSpectrum1323.graph
    sourceMap1078 fusedMap1078 sourceMap1078_checked fusedMap1078_checked
    DegreeOneSmallComparisons.comparison1078
#print axioms sourceMap1078_checked
#print axioms fusedMap1078_checked
#print axioms certified1078
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
