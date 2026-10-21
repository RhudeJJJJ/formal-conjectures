/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1905 : Family 10 := level10.get ⟨190,by decide⟩
def sourceMap1905 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1905 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1905_checked : acceptsGraphIso
    (source (graph core1905) (root 10) 0 0) DegreeOneSmallSpectrum989.graph sourceMap1905=true := by decide +kernel
theorem fusedMap1905_checked : acceptsGraphIso
    (fused (graph core1905) (root 10) 0 0) DegreeOneSmallSpectrum992.graph fusedMap1905=true := by decide +kernel
theorem certified1905 : Certified (graph core1905) (root 10) 0 0 :=
  of_native_maps core1905 DegreeOneSmallSpectrum989.graph DegreeOneSmallSpectrum992.graph
    sourceMap1905 fusedMap1905 sourceMap1905_checked fusedMap1905_checked
    DegreeOneSmallComparisons.comparison1905
#print axioms sourceMap1905_checked
#print axioms fusedMap1905_checked
#print axioms certified1905
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
