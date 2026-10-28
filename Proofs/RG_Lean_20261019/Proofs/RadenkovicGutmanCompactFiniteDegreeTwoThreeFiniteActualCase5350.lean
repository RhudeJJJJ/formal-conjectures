/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5350 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap5350 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5350 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5350_checked : acceptsGraphIso
    (source (graph core5350) (root 6) 3 4) DegreeTwoThreeSpectrum4646.graph sourceMap5350=true := by decide +kernel
theorem fusedMap5350_checked : acceptsGraphIso
    (fused (graph core5350) (root 6) 3 4) DegreeTwoThreeSpectrum3897.graph fusedMap5350=true := by decide +kernel
theorem certified5350 : Certified (graph core5350) (root 6) 3 4 :=
  of_native_maps core5350 DegreeTwoThreeSpectrum4646.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap5350 fusedMap5350 sourceMap5350_checked fusedMap5350_checked
    DegreeTwoThreeFiniteComparisons.comparison5350
#print axioms sourceMap5350_checked
#print axioms fusedMap5350_checked
#print axioms certified5350
def sourceMap5350swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5350swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5350swap_checked : acceptsGraphIso
    (source (graph core5350) (root 6) 4 3) DegreeTwoThreeSpectrum4646.graph sourceMap5350swap=true := by decide +kernel
theorem fusedMap5350swap_checked : acceptsGraphIso
    (fused (graph core5350) (root 6) 4 3) DegreeTwoThreeSpectrum3897.graph fusedMap5350swap=true := by decide +kernel
theorem certified5350swap : Certified (graph core5350) (root 6) 4 3 :=
  of_native_maps core5350 DegreeTwoThreeSpectrum4646.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap5350swap fusedMap5350swap sourceMap5350swap_checked fusedMap5350swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5350
#print axioms sourceMap5350swap_checked
#print axioms fusedMap5350swap_checked
#print axioms certified5350swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
