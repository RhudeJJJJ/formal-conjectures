/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3885 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap3885 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3885 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3885_checked : acceptsGraphIso
    (source (graph core3885) (root 8) 1 4) DegreeTwoThreeSpectrum4626.graph sourceMap3885=true := by decide +kernel
theorem fusedMap3885_checked : acceptsGraphIso
    (fused (graph core3885) (root 8) 1 4) DegreeTwoThreeSpectrum4115.graph fusedMap3885=true := by decide +kernel
theorem certified3885 : Certified (graph core3885) (root 8) 1 4 :=
  of_native_maps core3885 DegreeTwoThreeSpectrum4626.graph DegreeTwoThreeSpectrum4115.graph
    sourceMap3885 fusedMap3885 sourceMap3885_checked fusedMap3885_checked
    DegreeTwoThreeFiniteComparisons.comparison3885
#print axioms sourceMap3885_checked
#print axioms fusedMap3885_checked
#print axioms certified3885
def sourceMap3885swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3885swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3885swap_checked : acceptsGraphIso
    (source (graph core3885) (root 8) 4 1) DegreeTwoThreeSpectrum4626.graph sourceMap3885swap=true := by decide +kernel
theorem fusedMap3885swap_checked : acceptsGraphIso
    (fused (graph core3885) (root 8) 4 1) DegreeTwoThreeSpectrum4115.graph fusedMap3885swap=true := by decide +kernel
theorem certified3885swap : Certified (graph core3885) (root 8) 4 1 :=
  of_native_maps core3885 DegreeTwoThreeSpectrum4626.graph DegreeTwoThreeSpectrum4115.graph
    sourceMap3885swap fusedMap3885swap sourceMap3885swap_checked fusedMap3885swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3885
#print axioms sourceMap3885swap_checked
#print axioms fusedMap3885swap_checked
#print axioms certified3885swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
