/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0863 : Family 10 := level10.get ⟨1363,by decide⟩
def sourceMap0863 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0863 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0863_checked : acceptsGraphIso
    (source (graph core0863) (root 10) 0 0) DegreeOneSmallSpectrum1623.graph sourceMap0863=true := by decide +kernel
theorem fusedMap0863_checked : acceptsGraphIso
    (fused (graph core0863) (root 10) 0 0) DegreeOneSmallSpectrum1961.graph fusedMap0863=true := by decide +kernel
theorem certified0863 : Certified (graph core0863) (root 10) 0 0 :=
  of_native_maps core0863 DegreeOneSmallSpectrum1623.graph DegreeOneSmallSpectrum1961.graph
    sourceMap0863 fusedMap0863 sourceMap0863_checked fusedMap0863_checked
    DegreeTwoThreeFiniteComparisons.comparison0863
#print axioms sourceMap0863_checked
#print axioms fusedMap0863_checked
#print axioms certified0863
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
