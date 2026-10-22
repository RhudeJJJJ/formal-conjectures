/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3373 : Family 9 := level9.get ⟨431,by decide⟩
def sourceMap3373 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3373 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3373_checked : acceptsGraphIso
    (source (graph core3373) (root 9) 0 5) DegreeTwoThreeSpectrum6550.graph sourceMap3373=true := by decide +kernel
theorem fusedMap3373_checked : acceptsGraphIso
    (fused (graph core3373) (root 9) 0 5) DegreeTwoThreeSpectrum5447.graph fusedMap3373=true := by decide +kernel
theorem certified3373 : Certified (graph core3373) (root 9) 0 5 :=
  of_native_maps core3373 DegreeTwoThreeSpectrum6550.graph DegreeTwoThreeSpectrum5447.graph
    sourceMap3373 fusedMap3373 sourceMap3373_checked fusedMap3373_checked
    DegreeTwoThreeFiniteComparisons.comparison3373
#print axioms sourceMap3373_checked
#print axioms fusedMap3373_checked
#print axioms certified3373
def sourceMap3373swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3373swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3373swap_checked : acceptsGraphIso
    (source (graph core3373) (root 9) 5 0) DegreeTwoThreeSpectrum6550.graph sourceMap3373swap=true := by decide +kernel
theorem fusedMap3373swap_checked : acceptsGraphIso
    (fused (graph core3373) (root 9) 5 0) DegreeTwoThreeSpectrum5447.graph fusedMap3373swap=true := by decide +kernel
theorem certified3373swap : Certified (graph core3373) (root 9) 5 0 :=
  of_native_maps core3373 DegreeTwoThreeSpectrum6550.graph DegreeTwoThreeSpectrum5447.graph
    sourceMap3373swap fusedMap3373swap sourceMap3373swap_checked fusedMap3373swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3373
#print axioms sourceMap3373swap_checked
#print axioms fusedMap3373swap_checked
#print axioms certified3373swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
