/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3437 : Family 9 := level9.get ⟨580,by decide⟩
def sourceMap3437 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3437 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3437_checked : acceptsGraphIso
    (source (graph core3437) (root 9) 0 5) DegreeTwoThreeSpectrum6127.graph sourceMap3437=true := by decide +kernel
theorem fusedMap3437_checked : acceptsGraphIso
    (fused (graph core3437) (root 9) 0 5) DegreeTwoThreeSpectrum6128.graph fusedMap3437=true := by decide +kernel
theorem certified3437 : Certified (graph core3437) (root 9) 0 5 :=
  of_native_maps core3437 DegreeTwoThreeSpectrum6127.graph DegreeTwoThreeSpectrum6128.graph
    sourceMap3437 fusedMap3437 sourceMap3437_checked fusedMap3437_checked
    DegreeTwoThreeFiniteComparisons.comparison3437
#print axioms sourceMap3437_checked
#print axioms fusedMap3437_checked
#print axioms certified3437
def sourceMap3437swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3437swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3437swap_checked : acceptsGraphIso
    (source (graph core3437) (root 9) 5 0) DegreeTwoThreeSpectrum6127.graph sourceMap3437swap=true := by decide +kernel
theorem fusedMap3437swap_checked : acceptsGraphIso
    (fused (graph core3437) (root 9) 5 0) DegreeTwoThreeSpectrum6128.graph fusedMap3437swap=true := by decide +kernel
theorem certified3437swap : Certified (graph core3437) (root 9) 5 0 :=
  of_native_maps core3437 DegreeTwoThreeSpectrum6127.graph DegreeTwoThreeSpectrum6128.graph
    sourceMap3437swap fusedMap3437swap sourceMap3437swap_checked fusedMap3437swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3437
#print axioms sourceMap3437swap_checked
#print axioms fusedMap3437swap_checked
#print axioms certified3437swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
