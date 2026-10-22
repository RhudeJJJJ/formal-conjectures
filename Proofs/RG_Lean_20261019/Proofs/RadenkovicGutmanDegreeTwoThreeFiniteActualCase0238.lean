/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0238 : Family 9 := level9.get ⟨278,by decide⟩
def sourceMap0238 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0238 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0238_checked : acceptsGraphIso
    (source (graph core0238) (root 9) 0 0) DegreeOneSmallSpectrum640.graph sourceMap0238=true := by decide +kernel
theorem fusedMap0238_checked : acceptsGraphIso
    (fused (graph core0238) (root 9) 0 0) DegreeOneSmallSpectrum539.graph fusedMap0238=true := by decide +kernel
theorem certified0238 : Certified (graph core0238) (root 9) 0 0 :=
  of_native_maps core0238 DegreeOneSmallSpectrum640.graph DegreeOneSmallSpectrum539.graph
    sourceMap0238 fusedMap0238 sourceMap0238_checked fusedMap0238_checked
    DegreeTwoThreeFiniteComparisons.comparison0238
#print axioms sourceMap0238_checked
#print axioms fusedMap0238_checked
#print axioms certified0238
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
