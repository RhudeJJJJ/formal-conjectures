/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0088 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap0088 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0088 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0088_checked : acceptsGraphIso
    (source (graph core0088) (root 8) 0 0) DegreeOneSmallSpectrum225.graph sourceMap0088=true := by decide +kernel
theorem fusedMap0088_checked : acceptsGraphIso
    (fused (graph core0088) (root 8) 0 0) DegreeOneSmallSpectrum222.graph fusedMap0088=true := by decide +kernel
theorem certified0088 : Certified (graph core0088) (root 8) 0 0 :=
  of_native_maps core0088 DegreeOneSmallSpectrum225.graph DegreeOneSmallSpectrum222.graph
    sourceMap0088 fusedMap0088 sourceMap0088_checked fusedMap0088_checked
    DegreeTwoThreeFiniteComparisons.comparison0088
#print axioms sourceMap0088_checked
#print axioms fusedMap0088_checked
#print axioms certified0088
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
