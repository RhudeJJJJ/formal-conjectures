/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0467 : Family 10 := level10.get ⟨281,by decide⟩
def sourceMap0467 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0467 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0467_checked : acceptsGraphIso
    (source (graph core0467) (root 10) 0 0) DegreeOneSmallSpectrum1127.graph sourceMap0467=true := by decide +kernel
theorem fusedMap0467_checked : acceptsGraphIso
    (fused (graph core0467) (root 10) 0 0) DegreeOneSmallSpectrum1104.graph fusedMap0467=true := by decide +kernel
theorem certified0467 : Certified (graph core0467) (root 10) 0 0 :=
  of_native_maps core0467 DegreeOneSmallSpectrum1127.graph DegreeOneSmallSpectrum1104.graph
    sourceMap0467 fusedMap0467 sourceMap0467_checked fusedMap0467_checked
    DegreeTwoThreeFiniteComparisons.comparison0467
#print axioms sourceMap0467_checked
#print axioms fusedMap0467_checked
#print axioms certified0467
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
