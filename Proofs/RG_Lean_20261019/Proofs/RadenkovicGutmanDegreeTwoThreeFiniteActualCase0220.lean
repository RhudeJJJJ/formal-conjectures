/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0220 : Family 9 := level9.get ⟨224,by decide⟩
def sourceMap0220 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0220 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0220_checked : acceptsGraphIso
    (source (graph core0220) (root 9) 0 0) DegreeTwoThreeSpectrum455.graph sourceMap0220=true := by decide +kernel
theorem fusedMap0220_checked : acceptsGraphIso
    (fused (graph core0220) (root 9) 0 0) DegreeOneSmallSpectrum512.graph fusedMap0220=true := by decide +kernel
theorem certified0220 : Certified (graph core0220) (root 9) 0 0 :=
  of_native_maps core0220 DegreeTwoThreeSpectrum455.graph DegreeOneSmallSpectrum512.graph
    sourceMap0220 fusedMap0220 sourceMap0220_checked fusedMap0220_checked
    DegreeTwoThreeFiniteComparisons.comparison0220
#print axioms sourceMap0220_checked
#print axioms fusedMap0220_checked
#print axioms certified0220
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
