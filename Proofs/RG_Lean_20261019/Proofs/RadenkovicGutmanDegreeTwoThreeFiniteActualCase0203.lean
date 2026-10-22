/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0203 : Family 9 := level9.get ⟨172,by decide⟩
def sourceMap0203 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0203 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0203_checked : acceptsGraphIso
    (source (graph core0203) (root 9) 0 0) DegreeOneSmallSpectrum451.graph sourceMap0203=true := by decide +kernel
theorem fusedMap0203_checked : acceptsGraphIso
    (fused (graph core0203) (root 9) 0 0) DegreeOneSmallSpectrum450.graph fusedMap0203=true := by decide +kernel
theorem certified0203 : Certified (graph core0203) (root 9) 0 0 :=
  of_native_maps core0203 DegreeOneSmallSpectrum451.graph DegreeOneSmallSpectrum450.graph
    sourceMap0203 fusedMap0203 sourceMap0203_checked fusedMap0203_checked
    DegreeTwoThreeFiniteComparisons.comparison0203
#print axioms sourceMap0203_checked
#print axioms fusedMap0203_checked
#print axioms certified0203
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
