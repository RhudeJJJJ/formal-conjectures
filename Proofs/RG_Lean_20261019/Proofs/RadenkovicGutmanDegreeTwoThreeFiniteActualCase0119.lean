/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0119 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap0119 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0119 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0119_checked : acceptsGraphIso
    (source (graph core0119) (root 8) 0 0) DegreeOneSmallSpectrum338.graph sourceMap0119=true := by decide +kernel
theorem fusedMap0119_checked : acceptsGraphIso
    (fused (graph core0119) (root 8) 0 0) DegreeOneSmallSpectrum330.graph fusedMap0119=true := by decide +kernel
theorem certified0119 : Certified (graph core0119) (root 8) 0 0 :=
  of_native_maps core0119 DegreeOneSmallSpectrum338.graph DegreeOneSmallSpectrum330.graph
    sourceMap0119 fusedMap0119 sourceMap0119_checked fusedMap0119_checked
    DegreeTwoThreeFiniteComparisons.comparison0119
#print axioms sourceMap0119_checked
#print axioms fusedMap0119_checked
#print axioms certified0119
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
