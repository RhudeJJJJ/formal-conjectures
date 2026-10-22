/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0753 : Family 10 := level10.get ⟨1097,by decide⟩
def sourceMap0753 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0753 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0753_checked : acceptsGraphIso
    (source (graph core0753) (root 10) 0 0) DegreeOneSmallSpectrum1670.graph sourceMap0753=true := by decide +kernel
theorem fusedMap0753_checked : acceptsGraphIso
    (fused (graph core0753) (root 10) 0 0) DegreeOneSmallSpectrum1710.graph fusedMap0753=true := by decide +kernel
theorem certified0753 : Certified (graph core0753) (root 10) 0 0 :=
  of_native_maps core0753 DegreeOneSmallSpectrum1670.graph DegreeOneSmallSpectrum1710.graph
    sourceMap0753 fusedMap0753 sourceMap0753_checked fusedMap0753_checked
    DegreeTwoThreeFiniteComparisons.comparison0753
#print axioms sourceMap0753_checked
#print axioms fusedMap0753_checked
#print axioms certified0753
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
