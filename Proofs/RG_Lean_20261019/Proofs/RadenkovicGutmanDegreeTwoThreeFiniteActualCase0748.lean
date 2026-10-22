/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0748 : Family 10 := level10.get ⟨1082,by decide⟩
def sourceMap0748 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0748 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,12,7,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0748_checked : acceptsGraphIso
    (source (graph core0748) (root 10) 0 0) DegreeOneSmallSpectrum1678.graph sourceMap0748=true := by decide +kernel
theorem fusedMap0748_checked : acceptsGraphIso
    (fused (graph core0748) (root 10) 0 0) DegreeOneSmallSpectrum1675.graph fusedMap0748=true := by decide +kernel
theorem certified0748 : Certified (graph core0748) (root 10) 0 0 :=
  of_native_maps core0748 DegreeOneSmallSpectrum1678.graph DegreeOneSmallSpectrum1675.graph
    sourceMap0748 fusedMap0748 sourceMap0748_checked fusedMap0748_checked
    DegreeTwoThreeFiniteComparisons.comparison0748
#print axioms sourceMap0748_checked
#print axioms fusedMap0748_checked
#print axioms certified0748
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
