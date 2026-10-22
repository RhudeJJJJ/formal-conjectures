/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0236 : Family 9 := level9.get ⟨272,by decide⟩
def sourceMap0236 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0236 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0236_checked : acceptsGraphIso
    (source (graph core0236) (root 9) 0 0) DegreeOneSmallSpectrum657.graph sourceMap0236=true := by decide +kernel
theorem fusedMap0236_checked : acceptsGraphIso
    (fused (graph core0236) (root 9) 0 0) DegreeOneSmallSpectrum548.graph fusedMap0236=true := by decide +kernel
theorem certified0236 : Certified (graph core0236) (root 9) 0 0 :=
  of_native_maps core0236 DegreeOneSmallSpectrum657.graph DegreeOneSmallSpectrum548.graph
    sourceMap0236 fusedMap0236 sourceMap0236_checked fusedMap0236_checked
    DegreeTwoThreeFiniteComparisons.comparison0236
#print axioms sourceMap0236_checked
#print axioms fusedMap0236_checked
#print axioms certified0236
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
