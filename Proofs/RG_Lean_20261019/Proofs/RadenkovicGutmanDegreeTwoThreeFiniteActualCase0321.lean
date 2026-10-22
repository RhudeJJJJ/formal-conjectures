/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0321 : Family 9 := level9.get ⟨488,by decide⟩
def sourceMap0321 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 9 0 0 v)
def fusedMap0321 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0321_checked : acceptsGraphIso
    (source (graph core0321) (root 9) 0 0) DegreeOneSmallSpectrum825.graph sourceMap0321=true := by decide +kernel
theorem fusedMap0321_checked : acceptsGraphIso
    (fused (graph core0321) (root 9) 0 0) DegreeOneSmallSpectrum816.graph fusedMap0321=true := by decide +kernel
theorem certified0321 : Certified (graph core0321) (root 9) 0 0 :=
  of_native_maps core0321 DegreeOneSmallSpectrum825.graph DegreeOneSmallSpectrum816.graph
    sourceMap0321 fusedMap0321 sourceMap0321_checked fusedMap0321_checked
    DegreeTwoThreeFiniteComparisons.comparison0321
#print axioms sourceMap0321_checked
#print axioms fusedMap0321_checked
#print axioms certified0321
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
