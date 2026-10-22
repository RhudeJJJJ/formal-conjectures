/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0704 : Family 10 := level10.get ⟨967,by decide⟩
def sourceMap0704 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0704 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0704_checked : acceptsGraphIso
    (source (graph core0704) (root 10) 0 0) DegreeOneSmallSpectrum1226.graph sourceMap0704=true := by decide +kernel
theorem fusedMap0704_checked : acceptsGraphIso
    (fused (graph core0704) (root 10) 0 0) DegreeOneSmallSpectrum1211.graph fusedMap0704=true := by decide +kernel
theorem certified0704 : Certified (graph core0704) (root 10) 0 0 :=
  of_native_maps core0704 DegreeOneSmallSpectrum1226.graph DegreeOneSmallSpectrum1211.graph
    sourceMap0704 fusedMap0704 sourceMap0704_checked fusedMap0704_checked
    DegreeTwoThreeFiniteComparisons.comparison0704
#print axioms sourceMap0704_checked
#print axioms fusedMap0704_checked
#print axioms certified0704
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
