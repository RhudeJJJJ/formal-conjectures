/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0700 : Family 10 := level10.get ⟨960,by decide⟩
def sourceMap0700 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0700 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0700_checked : acceptsGraphIso
    (source (graph core0700) (root 10) 0 0) DegreeOneSmallSpectrum1371.graph sourceMap0700=true := by decide +kernel
theorem fusedMap0700_checked : acceptsGraphIso
    (fused (graph core0700) (root 10) 0 0) DegreeOneSmallSpectrum1320.graph fusedMap0700=true := by decide +kernel
theorem certified0700 : Certified (graph core0700) (root 10) 0 0 :=
  of_native_maps core0700 DegreeOneSmallSpectrum1371.graph DegreeOneSmallSpectrum1320.graph
    sourceMap0700 fusedMap0700 sourceMap0700_checked fusedMap0700_checked
    DegreeTwoThreeFiniteComparisons.comparison0700
#print axioms sourceMap0700_checked
#print axioms fusedMap0700_checked
#print axioms certified0700
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
