/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3057 : Family 10 := level10.get ⟨1719,by decide⟩
def sourceMap3057 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3057 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3057_checked : acceptsGraphIso
    (source (graph core3057) (root 10) 0 4) DegreeTwoThreeSpectrum7342.graph sourceMap3057=true := by decide +kernel
theorem fusedMap3057_checked : acceptsGraphIso
    (fused (graph core3057) (root 10) 0 4) DegreeTwoThreeSpectrum6506.graph fusedMap3057=true := by decide +kernel
theorem certified3057 : Certified (graph core3057) (root 10) 0 4 :=
  of_native_maps core3057 DegreeTwoThreeSpectrum7342.graph DegreeTwoThreeSpectrum6506.graph
    sourceMap3057 fusedMap3057 sourceMap3057_checked fusedMap3057_checked
    DegreeTwoThreeFiniteComparisons.comparison3057
#print axioms sourceMap3057_checked
#print axioms fusedMap3057_checked
#print axioms certified3057
def sourceMap3057swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3057swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3057swap_checked : acceptsGraphIso
    (source (graph core3057) (root 10) 4 0) DegreeTwoThreeSpectrum7342.graph sourceMap3057swap=true := by decide +kernel
theorem fusedMap3057swap_checked : acceptsGraphIso
    (fused (graph core3057) (root 10) 4 0) DegreeTwoThreeSpectrum6506.graph fusedMap3057swap=true := by decide +kernel
theorem certified3057swap : Certified (graph core3057) (root 10) 4 0 :=
  of_native_maps core3057 DegreeTwoThreeSpectrum7342.graph DegreeTwoThreeSpectrum6506.graph
    sourceMap3057swap fusedMap3057swap sourceMap3057swap_checked fusedMap3057swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3057
#print axioms sourceMap3057swap_checked
#print axioms fusedMap3057swap_checked
#print axioms certified3057swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
