/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5072 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap5072 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5072 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5072_checked : acceptsGraphIso
    (source (graph core5072) (root 6) 2 4) DegreeTwoThreeSpectrum3241.graph sourceMap5072=true := by decide +kernel
theorem fusedMap5072_checked : acceptsGraphIso
    (fused (graph core5072) (root 6) 2 4) DegreeTwoThreeSpectrum2323.graph fusedMap5072=true := by decide +kernel
theorem certified5072 : Certified (graph core5072) (root 6) 2 4 :=
  of_native_maps core5072 DegreeTwoThreeSpectrum3241.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap5072 fusedMap5072 sourceMap5072_checked fusedMap5072_checked
    DegreeTwoThreeFiniteComparisons.comparison5072
#print axioms sourceMap5072_checked
#print axioms fusedMap5072_checked
#print axioms certified5072
def sourceMap5072swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap5072swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5072swap_checked : acceptsGraphIso
    (source (graph core5072) (root 6) 4 2) DegreeTwoThreeSpectrum3241.graph sourceMap5072swap=true := by decide +kernel
theorem fusedMap5072swap_checked : acceptsGraphIso
    (fused (graph core5072) (root 6) 4 2) DegreeTwoThreeSpectrum2323.graph fusedMap5072swap=true := by decide +kernel
theorem certified5072swap : Certified (graph core5072) (root 6) 4 2 :=
  of_native_maps core5072 DegreeTwoThreeSpectrum3241.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap5072swap fusedMap5072swap sourceMap5072swap_checked fusedMap5072swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5072
#print axioms sourceMap5072swap_checked
#print axioms fusedMap5072swap_checked
#print axioms certified5072swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
