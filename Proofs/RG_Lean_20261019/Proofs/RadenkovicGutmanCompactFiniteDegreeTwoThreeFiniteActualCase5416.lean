/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5416 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5416 : (Vertices 2 ⊕ Fin 5 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,8,9,3,4,5,6,7,1,0,10,11,12,13,14,15,16] (sourceLabel 2 4 8 v)
def fusedMap5416 : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 4 8 v)
theorem sourceMap5416_checked : acceptsGraphIso
    (source (graph core5416) (root 2) 4 8) DegreeTwoThreeSpectrum5115.graph sourceMap5416=true := by decide +kernel
theorem fusedMap5416_checked : acceptsGraphIso
    (fused (graph core5416) (root 2) 4 8) DegreeTwoThreeSpectrum4959.graph fusedMap5416=true := by decide +kernel
theorem certified5416 : Certified (graph core5416) (root 2) 4 8 :=
  of_native_maps core5416 DegreeTwoThreeSpectrum5115.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5416 fusedMap5416 sourceMap5416_checked fusedMap5416_checked
    DegreeTwoThreeFiniteComparisons.comparison5416
#print axioms sourceMap5416_checked
#print axioms fusedMap5416_checked
#print axioms certified5416
def sourceMap5416swap : (Vertices 2 ⊕ Fin 9 ⊕ Fin 5) → Fin 17 :=
  fun v => ![2,8,9,1,0,10,11,12,13,14,15,16,3,4,5,6,7] (sourceLabel 2 8 4 v)
def fusedMap5416swap : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 8 4 v)
theorem sourceMap5416swap_checked : acceptsGraphIso
    (source (graph core5416) (root 2) 8 4) DegreeTwoThreeSpectrum5115.graph sourceMap5416swap=true := by decide +kernel
theorem fusedMap5416swap_checked : acceptsGraphIso
    (fused (graph core5416) (root 2) 8 4) DegreeTwoThreeSpectrum4959.graph fusedMap5416swap=true := by decide +kernel
theorem certified5416swap : Certified (graph core5416) (root 2) 8 4 :=
  of_native_maps core5416 DegreeTwoThreeSpectrum5115.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5416swap fusedMap5416swap sourceMap5416swap_checked fusedMap5416swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5416
#print axioms sourceMap5416swap_checked
#print axioms fusedMap5416swap_checked
#print axioms certified5416swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
