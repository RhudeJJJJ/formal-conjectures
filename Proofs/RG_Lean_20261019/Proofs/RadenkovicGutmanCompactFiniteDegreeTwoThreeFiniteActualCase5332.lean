/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5332 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5332 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4,10,11,12,13,14] (sourceLabel 5 3 4 v)
def fusedMap5332 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 3 4 v)
theorem sourceMap5332_checked : acceptsGraphIso
    (source (graph core5332) (root 5) 3 4) DegreeTwoThreeSpectrum2951.graph sourceMap5332=true := by decide +kernel
theorem fusedMap5332_checked : acceptsGraphIso
    (fused (graph core5332) (root 5) 3 4) DegreeTwoThreeSpectrum2365.graph fusedMap5332=true := by decide +kernel
theorem certified5332 : Certified (graph core5332) (root 5) 3 4 :=
  of_native_maps core5332 DegreeTwoThreeSpectrum2951.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap5332 fusedMap5332 sourceMap5332_checked fusedMap5332_checked
    DegreeTwoThreeFiniteComparisons.comparison5332
#print axioms sourceMap5332_checked
#print axioms fusedMap5332_checked
#print axioms certified5332
def sourceMap5332swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,1,2,3,4] (sourceLabel 5 4 3 v)
def fusedMap5332swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 4 3 v)
theorem sourceMap5332swap_checked : acceptsGraphIso
    (source (graph core5332) (root 5) 4 3) DegreeTwoThreeSpectrum2951.graph sourceMap5332swap=true := by decide +kernel
theorem fusedMap5332swap_checked : acceptsGraphIso
    (fused (graph core5332) (root 5) 4 3) DegreeTwoThreeSpectrum2365.graph fusedMap5332swap=true := by decide +kernel
theorem certified5332swap : Certified (graph core5332) (root 5) 4 3 :=
  of_native_maps core5332 DegreeTwoThreeSpectrum2951.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap5332swap fusedMap5332swap sourceMap5332swap_checked fusedMap5332swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5332
#print axioms sourceMap5332swap_checked
#print axioms fusedMap5332swap_checked
#print axioms certified5332swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
