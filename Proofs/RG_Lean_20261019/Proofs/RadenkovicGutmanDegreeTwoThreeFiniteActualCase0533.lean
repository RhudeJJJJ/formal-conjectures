/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0533 : Family 10 := level10.get ⟨489,by decide⟩
def sourceMap0533 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0533 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0533_checked : acceptsGraphIso
    (source (graph core0533) (root 10) 0 0) DegreeOneSmallSpectrum881.graph sourceMap0533=true := by decide +kernel
theorem fusedMap0533_checked : acceptsGraphIso
    (fused (graph core0533) (root 10) 0 0) DegreeOneSmallSpectrum880.graph fusedMap0533=true := by decide +kernel
theorem certified0533 : Certified (graph core0533) (root 10) 0 0 :=
  of_native_maps core0533 DegreeOneSmallSpectrum881.graph DegreeOneSmallSpectrum880.graph
    sourceMap0533 fusedMap0533 sourceMap0533_checked fusedMap0533_checked
    DegreeTwoThreeFiniteComparisons.comparison0533
#print axioms sourceMap0533_checked
#print axioms fusedMap0533_checked
#print axioms certified0533
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
