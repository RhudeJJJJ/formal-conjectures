/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0690 : Family 10 := level10.get ⟨938,by decide⟩
def sourceMap0690 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0690 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0690_checked : acceptsGraphIso
    (source (graph core0690) (root 10) 0 0) DegreeOneSmallSpectrum1365.graph sourceMap0690=true := by decide +kernel
theorem fusedMap0690_checked : acceptsGraphIso
    (fused (graph core0690) (root 10) 0 0) DegreeOneSmallSpectrum1314.graph fusedMap0690=true := by decide +kernel
theorem certified0690 : Certified (graph core0690) (root 10) 0 0 :=
  of_native_maps core0690 DegreeOneSmallSpectrum1365.graph DegreeOneSmallSpectrum1314.graph
    sourceMap0690 fusedMap0690 sourceMap0690_checked fusedMap0690_checked
    DegreeTwoThreeFiniteComparisons.comparison0690
#print axioms sourceMap0690_checked
#print axioms fusedMap0690_checked
#print axioms certified0690
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
