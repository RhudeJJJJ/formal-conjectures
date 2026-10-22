/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0746 : Family 10 := level10.get ⟨1079,by decide⟩
def sourceMap0746 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0746 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0746_checked : acceptsGraphIso
    (source (graph core0746) (root 10) 0 0) DegreeTwoThreeSpectrum1469.graph sourceMap0746=true := by decide +kernel
theorem fusedMap0746_checked : acceptsGraphIso
    (fused (graph core0746) (root 10) 0 0) DegreeOneSmallSpectrum1686.graph fusedMap0746=true := by decide +kernel
theorem certified0746 : Certified (graph core0746) (root 10) 0 0 :=
  of_native_maps core0746 DegreeTwoThreeSpectrum1469.graph DegreeOneSmallSpectrum1686.graph
    sourceMap0746 fusedMap0746 sourceMap0746_checked fusedMap0746_checked
    DegreeTwoThreeFiniteComparisons.comparison0746
#print axioms sourceMap0746_checked
#print axioms fusedMap0746_checked
#print axioms certified0746
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
