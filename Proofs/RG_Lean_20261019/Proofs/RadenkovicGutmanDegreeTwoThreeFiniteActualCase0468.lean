/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0468 : Family 10 := level10.get ⟨289,by decide⟩
def sourceMap0468 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0468 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0468_checked : acceptsGraphIso
    (source (graph core0468) (root 10) 0 0) DegreeTwoThreeSpectrum911.graph sourceMap0468=true := by decide +kernel
theorem fusedMap0468_checked : acceptsGraphIso
    (fused (graph core0468) (root 10) 0 0) DegreeOneSmallSpectrum1309.graph fusedMap0468=true := by decide +kernel
theorem certified0468 : Certified (graph core0468) (root 10) 0 0 :=
  of_native_maps core0468 DegreeTwoThreeSpectrum911.graph DegreeOneSmallSpectrum1309.graph
    sourceMap0468 fusedMap0468 sourceMap0468_checked fusedMap0468_checked
    DegreeTwoThreeFiniteComparisons.comparison0468
#print axioms sourceMap0468_checked
#print axioms fusedMap0468_checked
#print axioms certified0468
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
