/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0867 : Family 10 := level10.get ⟨1371,by decide⟩
def sourceMap0867 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0867 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0867_checked : acceptsGraphIso
    (source (graph core0867) (root 10) 0 0) DegreeOneSmallSpectrum1640.graph sourceMap0867=true := by decide +kernel
theorem fusedMap0867_checked : acceptsGraphIso
    (fused (graph core0867) (root 10) 0 0) DegreeOneSmallSpectrum1962.graph fusedMap0867=true := by decide +kernel
theorem certified0867 : Certified (graph core0867) (root 10) 0 0 :=
  of_native_maps core0867 DegreeOneSmallSpectrum1640.graph DegreeOneSmallSpectrum1962.graph
    sourceMap0867 fusedMap0867 sourceMap0867_checked fusedMap0867_checked
    DegreeTwoThreeFiniteComparisons.comparison0867
#print axioms sourceMap0867_checked
#print axioms fusedMap0867_checked
#print axioms certified0867
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
