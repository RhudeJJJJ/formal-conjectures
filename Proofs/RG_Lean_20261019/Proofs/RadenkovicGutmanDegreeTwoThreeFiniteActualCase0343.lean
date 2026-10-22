/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0343 : Family 9 := level9.get ⟨535,by decide⟩
def sourceMap0343 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap0343 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0343_checked : acceptsGraphIso
    (source (graph core0343) (root 9) 0 0) DegreeOneSmallSpectrum612.graph sourceMap0343=true := by decide +kernel
theorem fusedMap0343_checked : acceptsGraphIso
    (fused (graph core0343) (root 9) 0 0) DegreeOneSmallSpectrum608.graph fusedMap0343=true := by decide +kernel
theorem certified0343 : Certified (graph core0343) (root 9) 0 0 :=
  of_native_maps core0343 DegreeOneSmallSpectrum612.graph DegreeOneSmallSpectrum608.graph
    sourceMap0343 fusedMap0343 sourceMap0343_checked fusedMap0343_checked
    DegreeTwoThreeFiniteComparisons.comparison0343
#print axioms sourceMap0343_checked
#print axioms fusedMap0343_checked
#print axioms certified0343
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
