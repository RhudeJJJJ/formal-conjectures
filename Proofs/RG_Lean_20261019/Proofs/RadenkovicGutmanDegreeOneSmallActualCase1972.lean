/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1972 : Family 10 := level10.get ⟨291,by decide⟩
def sourceMap1972 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1972 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1972_checked : acceptsGraphIso
    (source (graph core1972) (root 10) 0 0) DegreeOneSmallSpectrum1255.graph sourceMap1972=true := by decide +kernel
theorem fusedMap1972_checked : acceptsGraphIso
    (fused (graph core1972) (root 10) 0 0) DegreeOneSmallSpectrum1323.graph fusedMap1972=true := by decide +kernel
theorem certified1972 : Certified (graph core1972) (root 10) 0 0 :=
  of_native_maps core1972 DegreeOneSmallSpectrum1255.graph DegreeOneSmallSpectrum1323.graph
    sourceMap1972 fusedMap1972 sourceMap1972_checked fusedMap1972_checked
    DegreeOneSmallComparisons.comparison1972
#print axioms sourceMap1972_checked
#print axioms fusedMap1972_checked
#print axioms certified1972
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
