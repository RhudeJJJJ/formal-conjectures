/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1942 : Family 10 := level10.get ⟨241,by decide⟩
def sourceMap1942 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1942 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1942_checked : acceptsGraphIso
    (source (graph core1942) (root 10) 0 0) DegreeOneSmallSpectrum1192.graph sourceMap1942=true := by decide +kernel
theorem fusedMap1942_checked : acceptsGraphIso
    (fused (graph core1942) (root 10) 0 0) DegreeOneSmallSpectrum1195.graph fusedMap1942=true := by decide +kernel
theorem certified1942 : Certified (graph core1942) (root 10) 0 0 :=
  of_native_maps core1942 DegreeOneSmallSpectrum1192.graph DegreeOneSmallSpectrum1195.graph
    sourceMap1942 fusedMap1942 sourceMap1942_checked fusedMap1942_checked
    DegreeOneSmallComparisons.comparison1942
#print axioms sourceMap1942_checked
#print axioms fusedMap1942_checked
#print axioms certified1942
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
