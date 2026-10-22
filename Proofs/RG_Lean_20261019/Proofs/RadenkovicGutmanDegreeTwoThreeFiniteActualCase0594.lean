/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0594 : Family 10 := level10.get ⟨674,by decide⟩
def sourceMap0594 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0594 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0594_checked : acceptsGraphIso
    (source (graph core0594) (root 10) 0 0) DegreeOneSmallSpectrum906.graph sourceMap0594=true := by decide +kernel
theorem fusedMap0594_checked : acceptsGraphIso
    (fused (graph core0594) (root 10) 0 0) DegreeOneSmallSpectrum905.graph fusedMap0594=true := by decide +kernel
theorem certified0594 : Certified (graph core0594) (root 10) 0 0 :=
  of_native_maps core0594 DegreeOneSmallSpectrum906.graph DegreeOneSmallSpectrum905.graph
    sourceMap0594 fusedMap0594 sourceMap0594_checked fusedMap0594_checked
    DegreeTwoThreeFiniteComparisons.comparison0594
#print axioms sourceMap0594_checked
#print axioms fusedMap0594_checked
#print axioms certified0594
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
