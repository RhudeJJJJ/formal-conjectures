/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0904 : Family 10 := level10.get ⟨1453,by decide⟩
def sourceMap0904 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0904 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0904_checked : acceptsGraphIso
    (source (graph core0904) (root 10) 0 0) DegreeOneSmallSpectrum1653.graph sourceMap0904=true := by decide +kernel
theorem fusedMap0904_checked : acceptsGraphIso
    (fused (graph core0904) (root 10) 0 0) DegreeOneSmallSpectrum1636.graph fusedMap0904=true := by decide +kernel
theorem certified0904 : Certified (graph core0904) (root 10) 0 0 :=
  of_native_maps core0904 DegreeOneSmallSpectrum1653.graph DegreeOneSmallSpectrum1636.graph
    sourceMap0904 fusedMap0904 sourceMap0904_checked fusedMap0904_checked
    DegreeTwoThreeFiniteComparisons.comparison0904
#print axioms sourceMap0904_checked
#print axioms fusedMap0904_checked
#print axioms certified0904
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
