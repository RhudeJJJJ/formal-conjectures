/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0705 : Family 10 := level10.get ⟨968,by decide⟩
def sourceMap0705 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0705 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0705_checked : acceptsGraphIso
    (source (graph core0705) (root 10) 0 0) DegreeOneSmallSpectrum1424.graph sourceMap0705=true := by decide +kernel
theorem fusedMap0705_checked : acceptsGraphIso
    (fused (graph core0705) (root 10) 0 0) DegreeOneSmallSpectrum1414.graph fusedMap0705=true := by decide +kernel
theorem certified0705 : Certified (graph core0705) (root 10) 0 0 :=
  of_native_maps core0705 DegreeOneSmallSpectrum1424.graph DegreeOneSmallSpectrum1414.graph
    sourceMap0705 fusedMap0705 sourceMap0705_checked fusedMap0705_checked
    DegreeTwoThreeFiniteComparisons.comparison0705
#print axioms sourceMap0705_checked
#print axioms fusedMap0705_checked
#print axioms certified0705
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
