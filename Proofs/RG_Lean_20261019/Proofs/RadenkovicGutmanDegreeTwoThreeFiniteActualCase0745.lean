/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0745 : Family 10 := level10.get ⟨1078,by decide⟩
def sourceMap0745 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0745 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0745_checked : acceptsGraphIso
    (source (graph core0745) (root 10) 0 0) DegreeTwoThreeSpectrum1398.graph sourceMap0745=true := by decide +kernel
theorem fusedMap0745_checked : acceptsGraphIso
    (fused (graph core0745) (root 10) 0 0) DegreeOneSmallSpectrum1690.graph fusedMap0745=true := by decide +kernel
theorem certified0745 : Certified (graph core0745) (root 10) 0 0 :=
  of_native_maps core0745 DegreeTwoThreeSpectrum1398.graph DegreeOneSmallSpectrum1690.graph
    sourceMap0745 fusedMap0745 sourceMap0745_checked fusedMap0745_checked
    DegreeTwoThreeFiniteComparisons.comparison0745
#print axioms sourceMap0745_checked
#print axioms fusedMap0745_checked
#print axioms certified0745
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
