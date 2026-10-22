/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0598 : Family 10 := level10.get ⟨686,by decide⟩
def sourceMap0598 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0598 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0598_checked : acceptsGraphIso
    (source (graph core0598) (root 10) 0 0) DegreeTwoThreeSpectrum1459.graph sourceMap0598=true := by decide +kernel
theorem fusedMap0598_checked : acceptsGraphIso
    (fused (graph core0598) (root 10) 0 0) DegreeOneSmallSpectrum1294.graph fusedMap0598=true := by decide +kernel
theorem certified0598 : Certified (graph core0598) (root 10) 0 0 :=
  of_native_maps core0598 DegreeTwoThreeSpectrum1459.graph DegreeOneSmallSpectrum1294.graph
    sourceMap0598 fusedMap0598 sourceMap0598_checked fusedMap0598_checked
    DegreeTwoThreeFiniteComparisons.comparison0598
#print axioms sourceMap0598_checked
#print axioms fusedMap0598_checked
#print axioms certified0598
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
