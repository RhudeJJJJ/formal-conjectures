/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1928 : Family 10 := level10.get ⟨221,by decide⟩
def sourceMap1928 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1928 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1928_checked : acceptsGraphIso
    (source (graph core1928) (root 10) 0 0) DegreeOneSmallSpectrum1115.graph sourceMap1928=true := by decide +kernel
theorem fusedMap1928_checked : acceptsGraphIso
    (fused (graph core1928) (root 10) 0 0) DegreeOneSmallSpectrum1118.graph fusedMap1928=true := by decide +kernel
theorem certified1928 : Certified (graph core1928) (root 10) 0 0 :=
  of_native_maps core1928 DegreeOneSmallSpectrum1115.graph DegreeOneSmallSpectrum1118.graph
    sourceMap1928 fusedMap1928 sourceMap1928_checked fusedMap1928_checked
    DegreeOneSmallComparisons.comparison1928
#print axioms sourceMap1928_checked
#print axioms fusedMap1928_checked
#print axioms certified1928
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
