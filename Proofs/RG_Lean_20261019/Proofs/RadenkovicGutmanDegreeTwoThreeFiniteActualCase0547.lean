/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0547 : Family 10 := level10.get ⟨541,by decide⟩
def sourceMap0547 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0547 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0547_checked : acceptsGraphIso
    (source (graph core0547) (root 10) 0 0) DegreeTwoThreeSpectrum1442.graph sourceMap0547=true := by decide +kernel
theorem fusedMap0547_checked : acceptsGraphIso
    (fused (graph core0547) (root 10) 0 0) DegreeOneSmallSpectrum1047.graph fusedMap0547=true := by decide +kernel
theorem certified0547 : Certified (graph core0547) (root 10) 0 0 :=
  of_native_maps core0547 DegreeTwoThreeSpectrum1442.graph DegreeOneSmallSpectrum1047.graph
    sourceMap0547 fusedMap0547 sourceMap0547_checked fusedMap0547_checked
    DegreeTwoThreeFiniteComparisons.comparison0547
#print axioms sourceMap0547_checked
#print axioms fusedMap0547_checked
#print axioms certified0547
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
