/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0556 : Family 10 := level10.get ⟨567,by decide⟩
def sourceMap0556 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0556 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0556_checked : acceptsGraphIso
    (source (graph core0556) (root 10) 0 0) DegreeOneSmallSpectrum1674.graph sourceMap0556=true := by decide +kernel
theorem fusedMap0556_checked : acceptsGraphIso
    (fused (graph core0556) (root 10) 0 0) DegreeOneSmallSpectrum1093.graph fusedMap0556=true := by decide +kernel
theorem certified0556 : Certified (graph core0556) (root 10) 0 0 :=
  of_native_maps core0556 DegreeOneSmallSpectrum1674.graph DegreeOneSmallSpectrum1093.graph
    sourceMap0556 fusedMap0556 sourceMap0556_checked fusedMap0556_checked
    DegreeTwoThreeFiniteComparisons.comparison0556
#print axioms sourceMap0556_checked
#print axioms fusedMap0556_checked
#print axioms certified0556
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
