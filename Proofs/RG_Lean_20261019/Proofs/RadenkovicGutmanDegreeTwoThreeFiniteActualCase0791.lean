/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0791 : Family 10 := level10.get ⟨1192,by decide⟩
def sourceMap0791 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0791 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0791_checked : acceptsGraphIso
    (source (graph core0791) (root 10) 0 0) DegreeOneSmallSpectrum1866.graph sourceMap0791=true := by decide +kernel
theorem fusedMap0791_checked : acceptsGraphIso
    (fused (graph core0791) (root 10) 0 0) DegreeOneSmallSpectrum1857.graph fusedMap0791=true := by decide +kernel
theorem certified0791 : Certified (graph core0791) (root 10) 0 0 :=
  of_native_maps core0791 DegreeOneSmallSpectrum1866.graph DegreeOneSmallSpectrum1857.graph
    sourceMap0791 fusedMap0791 sourceMap0791_checked fusedMap0791_checked
    DegreeTwoThreeFiniteComparisons.comparison0791
#print axioms sourceMap0791_checked
#print axioms fusedMap0791_checked
#print axioms certified0791
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
