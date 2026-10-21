/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1817 : Family 10 := level10.get ⟨61,by decide⟩
def sourceMap1817 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1817 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1817_checked : acceptsGraphIso
    (source (graph core1817) (root 10) 0 0) DegreeOneSmallSpectrum1127.graph sourceMap1817=true := by decide +kernel
theorem fusedMap1817_checked : acceptsGraphIso
    (fused (graph core1817) (root 10) 0 0) DegreeOneSmallSpectrum872.graph fusedMap1817=true := by decide +kernel
theorem certified1817 : Certified (graph core1817) (root 10) 0 0 :=
  of_native_maps core1817 DegreeOneSmallSpectrum1127.graph DegreeOneSmallSpectrum872.graph
    sourceMap1817 fusedMap1817 sourceMap1817_checked fusedMap1817_checked
    DegreeOneSmallComparisons.comparison1817
#print axioms sourceMap1817_checked
#print axioms fusedMap1817_checked
#print axioms certified1817
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
