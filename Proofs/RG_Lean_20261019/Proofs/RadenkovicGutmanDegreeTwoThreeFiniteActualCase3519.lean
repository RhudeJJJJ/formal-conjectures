/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3519 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap3519 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3519 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3519_checked : acceptsGraphIso
    (source (graph core3519) (root 7) 0 6) DegreeTwoThreeSpectrum4118.graph sourceMap3519=true := by decide +kernel
theorem fusedMap3519_checked : acceptsGraphIso
    (fused (graph core3519) (root 7) 0 6) DegreeTwoThreeSpectrum4120.graph fusedMap3519=true := by decide +kernel
theorem certified3519 : Certified (graph core3519) (root 7) 0 6 :=
  of_native_maps core3519 DegreeTwoThreeSpectrum4118.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap3519 fusedMap3519 sourceMap3519_checked fusedMap3519_checked
    DegreeTwoThreeFiniteComparisons.comparison3519
#print axioms sourceMap3519_checked
#print axioms fusedMap3519_checked
#print axioms certified3519
def sourceMap3519swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3519swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3519swap_checked : acceptsGraphIso
    (source (graph core3519) (root 7) 6 0) DegreeTwoThreeSpectrum4118.graph sourceMap3519swap=true := by decide +kernel
theorem fusedMap3519swap_checked : acceptsGraphIso
    (fused (graph core3519) (root 7) 6 0) DegreeTwoThreeSpectrum4120.graph fusedMap3519swap=true := by decide +kernel
theorem certified3519swap : Certified (graph core3519) (root 7) 6 0 :=
  of_native_maps core3519 DegreeTwoThreeSpectrum4118.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap3519swap fusedMap3519swap sourceMap3519swap_checked fusedMap3519swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3519
#print axioms sourceMap3519swap_checked
#print axioms fusedMap3519swap_checked
#print axioms certified3519swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
