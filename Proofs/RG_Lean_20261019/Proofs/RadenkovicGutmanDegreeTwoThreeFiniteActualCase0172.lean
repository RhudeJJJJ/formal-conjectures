/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0172 : Family 9 := level9.get ⟨66,by decide⟩
def sourceMap0172 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0172 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0172_checked : acceptsGraphIso
    (source (graph core0172) (root 9) 0 0) DegreeOneSmallSpectrum408.graph sourceMap0172=true := by decide +kernel
theorem fusedMap0172_checked : acceptsGraphIso
    (fused (graph core0172) (root 9) 0 0) DegreeOneSmallSpectrum489.graph fusedMap0172=true := by decide +kernel
theorem certified0172 : Certified (graph core0172) (root 9) 0 0 :=
  of_native_maps core0172 DegreeOneSmallSpectrum408.graph DegreeOneSmallSpectrum489.graph
    sourceMap0172 fusedMap0172 sourceMap0172_checked fusedMap0172_checked
    DegreeTwoThreeFiniteComparisons.comparison0172
#print axioms sourceMap0172_checked
#print axioms fusedMap0172_checked
#print axioms certified0172
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
