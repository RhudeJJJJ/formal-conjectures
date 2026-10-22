/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0736 : Family 10 := level10.get ⟨1056,by decide⟩
def sourceMap0736 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0736 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0736_checked : acceptsGraphIso
    (source (graph core0736) (root 10) 0 0) DegreeTwoThreeSpectrum1381.graph sourceMap0736=true := by decide +kernel
theorem fusedMap0736_checked : acceptsGraphIso
    (fused (graph core0736) (root 10) 0 0) DegreeOneSmallSpectrum1664.graph fusedMap0736=true := by decide +kernel
theorem certified0736 : Certified (graph core0736) (root 10) 0 0 :=
  of_native_maps core0736 DegreeTwoThreeSpectrum1381.graph DegreeOneSmallSpectrum1664.graph
    sourceMap0736 fusedMap0736 sourceMap0736_checked fusedMap0736_checked
    DegreeTwoThreeFiniteComparisons.comparison0736
#print axioms sourceMap0736_checked
#print axioms fusedMap0736_checked
#print axioms certified0736
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
