/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0826 : Family 10 := level10.get ⟨1277,by decide⟩
def sourceMap0826 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0826 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0826_checked : acceptsGraphIso
    (source (graph core0826) (root 10) 0 0) DegreeOneSmallSpectrum1627.graph sourceMap0826=true := by decide +kernel
theorem fusedMap0826_checked : acceptsGraphIso
    (fused (graph core0826) (root 10) 0 0) DegreeOneSmallSpectrum1924.graph fusedMap0826=true := by decide +kernel
theorem certified0826 : Certified (graph core0826) (root 10) 0 0 :=
  of_native_maps core0826 DegreeOneSmallSpectrum1627.graph DegreeOneSmallSpectrum1924.graph
    sourceMap0826 fusedMap0826 sourceMap0826_checked fusedMap0826_checked
    DegreeTwoThreeFiniteComparisons.comparison0826
#print axioms sourceMap0826_checked
#print axioms fusedMap0826_checked
#print axioms certified0826
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
