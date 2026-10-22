/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0914 : Family 10 := level10.get ⟨1477,by decide⟩
def sourceMap0914 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0914 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0914_checked : acceptsGraphIso
    (source (graph core0914) (root 10) 0 0) DegreeOneSmallSpectrum1048.graph sourceMap0914=true := by decide +kernel
theorem fusedMap0914_checked : acceptsGraphIso
    (fused (graph core0914) (root 10) 0 0) DegreeOneSmallSpectrum1043.graph fusedMap0914=true := by decide +kernel
theorem certified0914 : Certified (graph core0914) (root 10) 0 0 :=
  of_native_maps core0914 DegreeOneSmallSpectrum1048.graph DegreeOneSmallSpectrum1043.graph
    sourceMap0914 fusedMap0914 sourceMap0914_checked fusedMap0914_checked
    DegreeTwoThreeFiniteComparisons.comparison0914
#print axioms sourceMap0914_checked
#print axioms fusedMap0914_checked
#print axioms certified0914
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
