/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0240 : Family 9 := level9.get ⟨281,by decide⟩
def sourceMap0240 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0240 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0240_checked : acceptsGraphIso
    (source (graph core0240) (root 9) 0 0) DegreeOneSmallSpectrum527.graph sourceMap0240=true := by decide +kernel
theorem fusedMap0240_checked : acceptsGraphIso
    (fused (graph core0240) (root 9) 0 0) DegreeOneSmallSpectrum509.graph fusedMap0240=true := by decide +kernel
theorem certified0240 : Certified (graph core0240) (root 9) 0 0 :=
  of_native_maps core0240 DegreeOneSmallSpectrum527.graph DegreeOneSmallSpectrum509.graph
    sourceMap0240 fusedMap0240 sourceMap0240_checked fusedMap0240_checked
    DegreeTwoThreeFiniteComparisons.comparison0240
#print axioms sourceMap0240_checked
#print axioms fusedMap0240_checked
#print axioms certified0240
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
