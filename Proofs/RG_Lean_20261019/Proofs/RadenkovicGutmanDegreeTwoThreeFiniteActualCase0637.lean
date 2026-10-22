/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0637 : Family 10 := level10.get ⟨797,by decide⟩
def sourceMap0637 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0637 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0637_checked : acceptsGraphIso
    (source (graph core0637) (root 10) 0 0) DegreeOneSmallSpectrum1130.graph sourceMap0637=true := by decide +kernel
theorem fusedMap0637_checked : acceptsGraphIso
    (fused (graph core0637) (root 10) 0 0) DegreeOneSmallSpectrum1107.graph fusedMap0637=true := by decide +kernel
theorem certified0637 : Certified (graph core0637) (root 10) 0 0 :=
  of_native_maps core0637 DegreeOneSmallSpectrum1130.graph DegreeOneSmallSpectrum1107.graph
    sourceMap0637 fusedMap0637 sourceMap0637_checked fusedMap0637_checked
    DegreeTwoThreeFiniteComparisons.comparison0637
#print axioms sourceMap0637_checked
#print axioms fusedMap0637_checked
#print axioms certified0637
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
