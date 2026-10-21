/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1846 : Family 10 := level10.get ⟨99,by decide⟩
def sourceMap1846 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1846 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1846_checked : acceptsGraphIso
    (source (graph core1846) (root 10) 0 0) DegreeOneSmallSpectrum1268.graph sourceMap1846=true := by decide +kernel
theorem fusedMap1846_checked : acceptsGraphIso
    (fused (graph core1846) (root 10) 0 0) DegreeOneSmallSpectrum923.graph fusedMap1846=true := by decide +kernel
theorem certified1846 : Certified (graph core1846) (root 10) 0 0 :=
  of_native_maps core1846 DegreeOneSmallSpectrum1268.graph DegreeOneSmallSpectrum923.graph
    sourceMap1846 fusedMap1846 sourceMap1846_checked fusedMap1846_checked
    DegreeOneSmallComparisons.comparison1846
#print axioms sourceMap1846_checked
#print axioms fusedMap1846_checked
#print axioms certified1846
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
