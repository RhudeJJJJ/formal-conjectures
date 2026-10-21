/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1841 : Family 10 := level10.get ⟨93,by decide⟩
def sourceMap1841 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1841 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1841_checked : acceptsGraphIso
    (source (graph core1841) (root 10) 0 0) DegreeOneSmallSpectrum1260.graph sourceMap1841=true := by decide +kernel
theorem fusedMap1841_checked : acceptsGraphIso
    (fused (graph core1841) (root 10) 0 0) DegreeOneSmallSpectrum916.graph fusedMap1841=true := by decide +kernel
theorem certified1841 : Certified (graph core1841) (root 10) 0 0 :=
  of_native_maps core1841 DegreeOneSmallSpectrum1260.graph DegreeOneSmallSpectrum916.graph
    sourceMap1841 fusedMap1841 sourceMap1841_checked fusedMap1841_checked
    DegreeOneSmallComparisons.comparison1841
#print axioms sourceMap1841_checked
#print axioms fusedMap1841_checked
#print axioms certified1841
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
