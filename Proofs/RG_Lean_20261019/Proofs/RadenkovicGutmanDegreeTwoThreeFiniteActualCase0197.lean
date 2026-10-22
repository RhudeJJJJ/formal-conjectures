/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0197 : Family 9 := level9.get ⟨153,by decide⟩
def sourceMap0197 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0197 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0197_checked : acceptsGraphIso
    (source (graph core0197) (root 9) 0 0) DegreeTwoThreeSpectrum563.graph sourceMap0197=true := by decide +kernel
theorem fusedMap0197_checked : acceptsGraphIso
    (fused (graph core0197) (root 9) 0 0) DegreeOneSmallSpectrum422.graph fusedMap0197=true := by decide +kernel
theorem certified0197 : Certified (graph core0197) (root 9) 0 0 :=
  of_native_maps core0197 DegreeTwoThreeSpectrum563.graph DegreeOneSmallSpectrum422.graph
    sourceMap0197 fusedMap0197 sourceMap0197_checked fusedMap0197_checked
    DegreeTwoThreeFiniteComparisons.comparison0197
#print axioms sourceMap0197_checked
#print axioms fusedMap0197_checked
#print axioms certified0197
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
