/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0194 : Family 9 := level9.get ⟨141,by decide⟩
def sourceMap0194 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0194 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0194_checked : acceptsGraphIso
    (source (graph core0194) (root 9) 0 0) DegreeTwoThreeSpectrum526.graph sourceMap0194=true := by decide +kernel
theorem fusedMap0194_checked : acceptsGraphIso
    (fused (graph core0194) (root 9) 0 0) DegreeOneSmallSpectrum402.graph fusedMap0194=true := by decide +kernel
theorem certified0194 : Certified (graph core0194) (root 9) 0 0 :=
  of_native_maps core0194 DegreeTwoThreeSpectrum526.graph DegreeOneSmallSpectrum402.graph
    sourceMap0194 fusedMap0194 sourceMap0194_checked fusedMap0194_checked
    DegreeTwoThreeFiniteComparisons.comparison0194
#print axioms sourceMap0194_checked
#print axioms fusedMap0194_checked
#print axioms certified0194
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
