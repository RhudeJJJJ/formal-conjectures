/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0663 : Family 10 := level10.get ⟨869,by decide⟩
def sourceMap0663 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0663 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0663_checked : acceptsGraphIso
    (source (graph core0663) (root 10) 0 0) DegreeOneSmallSpectrum1377.graph sourceMap0663=true := by decide +kernel
theorem fusedMap0663_checked : acceptsGraphIso
    (fused (graph core0663) (root 10) 0 0) DegreeOneSmallSpectrum1328.graph fusedMap0663=true := by decide +kernel
theorem certified0663 : Certified (graph core0663) (root 10) 0 0 :=
  of_native_maps core0663 DegreeOneSmallSpectrum1377.graph DegreeOneSmallSpectrum1328.graph
    sourceMap0663 fusedMap0663 sourceMap0663_checked fusedMap0663_checked
    DegreeTwoThreeFiniteComparisons.comparison0663
#print axioms sourceMap0663_checked
#print axioms fusedMap0663_checked
#print axioms certified0663
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
