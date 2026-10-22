/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3113 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap3113 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3113 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3113_checked : acceptsGraphIso
    (source (graph core3113) (root 7) 0 5) DegreeTwoThreeSpectrum2678.graph sourceMap3113=true := by decide +kernel
theorem fusedMap3113_checked : acceptsGraphIso
    (fused (graph core3113) (root 7) 0 5) DegreeTwoThreeSpectrum2351.graph fusedMap3113=true := by decide +kernel
theorem certified3113 : Certified (graph core3113) (root 7) 0 5 :=
  of_native_maps core3113 DegreeTwoThreeSpectrum2678.graph DegreeTwoThreeSpectrum2351.graph
    sourceMap3113 fusedMap3113 sourceMap3113_checked fusedMap3113_checked
    DegreeTwoThreeFiniteComparisons.comparison3113
#print axioms sourceMap3113_checked
#print axioms fusedMap3113_checked
#print axioms certified3113
def sourceMap3113swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3113swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3113swap_checked : acceptsGraphIso
    (source (graph core3113) (root 7) 5 0) DegreeTwoThreeSpectrum2678.graph sourceMap3113swap=true := by decide +kernel
theorem fusedMap3113swap_checked : acceptsGraphIso
    (fused (graph core3113) (root 7) 5 0) DegreeTwoThreeSpectrum2351.graph fusedMap3113swap=true := by decide +kernel
theorem certified3113swap : Certified (graph core3113) (root 7) 5 0 :=
  of_native_maps core3113 DegreeTwoThreeSpectrum2678.graph DegreeTwoThreeSpectrum2351.graph
    sourceMap3113swap fusedMap3113swap sourceMap3113swap_checked fusedMap3113swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3113
#print axioms sourceMap3113swap_checked
#print axioms fusedMap3113swap_checked
#print axioms certified3113swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
