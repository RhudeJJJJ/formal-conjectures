/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0916 : Family 10 := level10.get ⟨1480,by decide⟩
def sourceMap0916 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0916 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0916_checked : acceptsGraphIso
    (source (graph core0916) (root 10) 0 0) DegreeOneSmallSpectrum1322.graph sourceMap0916=true := by decide +kernel
theorem fusedMap0916_checked : acceptsGraphIso
    (fused (graph core0916) (root 10) 0 0) DegreeOneSmallSpectrum1318.graph fusedMap0916=true := by decide +kernel
theorem certified0916 : Certified (graph core0916) (root 10) 0 0 :=
  of_native_maps core0916 DegreeOneSmallSpectrum1322.graph DegreeOneSmallSpectrum1318.graph
    sourceMap0916 fusedMap0916 sourceMap0916_checked fusedMap0916_checked
    DegreeTwoThreeFiniteComparisons.comparison0916
#print axioms sourceMap0916_checked
#print axioms fusedMap0916_checked
#print axioms certified0916
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
