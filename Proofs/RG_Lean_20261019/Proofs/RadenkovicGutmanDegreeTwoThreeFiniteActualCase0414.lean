/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0414 : Family 10 := level10.get ⟨85,by decide⟩
def sourceMap0414 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0414 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0414_checked : acceptsGraphIso
    (source (graph core0414) (root 10) 0 0) DegreeOneSmallSpectrum897.graph sourceMap0414=true := by decide +kernel
theorem fusedMap0414_checked : acceptsGraphIso
    (fused (graph core0414) (root 10) 0 0) DegreeOneSmallSpectrum896.graph fusedMap0414=true := by decide +kernel
theorem certified0414 : Certified (graph core0414) (root 10) 0 0 :=
  of_native_maps core0414 DegreeOneSmallSpectrum897.graph DegreeOneSmallSpectrum896.graph
    sourceMap0414 fusedMap0414 sourceMap0414_checked fusedMap0414_checked
    DegreeTwoThreeFiniteComparisons.comparison0414
#print axioms sourceMap0414_checked
#print axioms fusedMap0414_checked
#print axioms certified0414
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
