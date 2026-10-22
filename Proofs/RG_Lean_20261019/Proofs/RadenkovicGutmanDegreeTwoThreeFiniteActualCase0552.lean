/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0552 : Family 10 := level10.get ⟨553,by decide⟩
def sourceMap0552 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0552 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0552_checked : acceptsGraphIso
    (source (graph core0552) (root 10) 0 0) DegreeTwoThreeSpectrum915.graph sourceMap0552=true := by decide +kernel
theorem fusedMap0552_checked : acceptsGraphIso
    (fused (graph core0552) (root 10) 0 0) DegreeOneSmallSpectrum1068.graph fusedMap0552=true := by decide +kernel
theorem certified0552 : Certified (graph core0552) (root 10) 0 0 :=
  of_native_maps core0552 DegreeTwoThreeSpectrum915.graph DegreeOneSmallSpectrum1068.graph
    sourceMap0552 fusedMap0552 sourceMap0552_checked fusedMap0552_checked
    DegreeTwoThreeFiniteComparisons.comparison0552
#print axioms sourceMap0552_checked
#print axioms fusedMap0552_checked
#print axioms certified0552
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
