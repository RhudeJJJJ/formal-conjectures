/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0942 : Family 10 := level10.get ⟨1559,by decide⟩
def sourceMap0942 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0942 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0942_checked : acceptsGraphIso
    (source (graph core0942) (root 10) 0 0) DegreeOneSmallSpectrum1596.graph sourceMap0942=true := by decide +kernel
theorem fusedMap0942_checked : acceptsGraphIso
    (fused (graph core0942) (root 10) 0 0) DegreeOneSmallSpectrum1595.graph fusedMap0942=true := by decide +kernel
theorem certified0942 : Certified (graph core0942) (root 10) 0 0 :=
  of_native_maps core0942 DegreeOneSmallSpectrum1596.graph DegreeOneSmallSpectrum1595.graph
    sourceMap0942 fusedMap0942 sourceMap0942_checked fusedMap0942_checked
    DegreeTwoThreeFiniteComparisons.comparison0942
#print axioms sourceMap0942_checked
#print axioms fusedMap0942_checked
#print axioms certified0942
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
