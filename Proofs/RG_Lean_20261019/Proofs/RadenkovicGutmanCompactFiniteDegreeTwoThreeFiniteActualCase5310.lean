/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5310 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5310 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,6,7,8,9,3,4,5,1,0,10,11,12,13,14,15] (sourceLabel 4 2 7 v)
def fusedMap5310 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 2 7 v)
theorem sourceMap5310_checked : acceptsGraphIso
    (source (graph core5310) (root 4) 2 7) DegreeTwoThreeSpectrum4068.graph sourceMap5310=true := by decide +kernel
theorem fusedMap5310_checked : acceptsGraphIso
    (fused (graph core5310) (root 4) 2 7) DegreeTwoThreeSpectrum3862.graph fusedMap5310=true := by decide +kernel
theorem certified5310 : Certified (graph core5310) (root 4) 2 7 :=
  of_native_maps core5310 DegreeTwoThreeSpectrum4068.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap5310 fusedMap5310 sourceMap5310_checked fusedMap5310_checked
    DegreeTwoThreeFiniteComparisons.comparison5310
#print axioms sourceMap5310_checked
#print axioms fusedMap5310_checked
#print axioms certified5310
def sourceMap5310swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,6,7,8,9,1,0,10,11,12,13,14,15,3,4,5] (sourceLabel 4 7 2 v)
def fusedMap5310swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 7 2 v)
theorem sourceMap5310swap_checked : acceptsGraphIso
    (source (graph core5310) (root 4) 7 2) DegreeTwoThreeSpectrum4068.graph sourceMap5310swap=true := by decide +kernel
theorem fusedMap5310swap_checked : acceptsGraphIso
    (fused (graph core5310) (root 4) 7 2) DegreeTwoThreeSpectrum3862.graph fusedMap5310swap=true := by decide +kernel
theorem certified5310swap : Certified (graph core5310) (root 4) 7 2 :=
  of_native_maps core5310 DegreeTwoThreeSpectrum4068.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap5310swap fusedMap5310swap sourceMap5310swap_checked fusedMap5310swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5310
#print axioms sourceMap5310swap_checked
#print axioms fusedMap5310swap_checked
#print axioms certified5310swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
