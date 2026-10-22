/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0913 : Family 10 := level10.get ⟨1475,by decide⟩
def sourceMap0913 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0913 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0913_checked : acceptsGraphIso
    (source (graph core0913) (root 10) 0 0) DegreeOneSmallSpectrum1503.graph sourceMap0913=true := by decide +kernel
theorem fusedMap0913_checked : acceptsGraphIso
    (fused (graph core0913) (root 10) 0 0) DegreeOneSmallSpectrum1502.graph fusedMap0913=true := by decide +kernel
theorem certified0913 : Certified (graph core0913) (root 10) 0 0 :=
  of_native_maps core0913 DegreeOneSmallSpectrum1503.graph DegreeOneSmallSpectrum1502.graph
    sourceMap0913 fusedMap0913 sourceMap0913_checked fusedMap0913_checked
    DegreeTwoThreeFiniteComparisons.comparison0913
#print axioms sourceMap0913_checked
#print axioms fusedMap0913_checked
#print axioms certified0913
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
