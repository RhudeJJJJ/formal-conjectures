/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0462 : Family 10 := level10.get ⟨270,by decide⟩
def sourceMap0462 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0462 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0462_checked : acceptsGraphIso
    (source (graph core0462) (root 10) 0 0) DegreeOneSmallSpectrum1264.graph sourceMap0462=true := by decide +kernel
theorem fusedMap0462_checked : acceptsGraphIso
    (fused (graph core0462) (root 10) 0 0) DegreeOneSmallSpectrum1257.graph fusedMap0462=true := by decide +kernel
theorem certified0462 : Certified (graph core0462) (root 10) 0 0 :=
  of_native_maps core0462 DegreeOneSmallSpectrum1264.graph DegreeOneSmallSpectrum1257.graph
    sourceMap0462 fusedMap0462 sourceMap0462_checked fusedMap0462_checked
    DegreeTwoThreeFiniteComparisons.comparison0462
#print axioms sourceMap0462_checked
#print axioms fusedMap0462_checked
#print axioms certified0462
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
