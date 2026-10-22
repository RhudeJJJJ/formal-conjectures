/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0442 : Family 10 := level10.get ⟨194,by decide⟩
def sourceMap0442 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0442 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0442_checked : acceptsGraphIso
    (source (graph core0442) (root 10) 0 0) DegreeTwoThreeSpectrum839.graph sourceMap0442=true := by decide +kernel
theorem fusedMap0442_checked : acceptsGraphIso
    (fused (graph core0442) (root 10) 0 0) DegreeOneSmallSpectrum1004.graph fusedMap0442=true := by decide +kernel
theorem certified0442 : Certified (graph core0442) (root 10) 0 0 :=
  of_native_maps core0442 DegreeTwoThreeSpectrum839.graph DegreeOneSmallSpectrum1004.graph
    sourceMap0442 fusedMap0442 sourceMap0442_checked fusedMap0442_checked
    DegreeTwoThreeFiniteComparisons.comparison0442
#print axioms sourceMap0442_checked
#print axioms fusedMap0442_checked
#print axioms certified0442
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
