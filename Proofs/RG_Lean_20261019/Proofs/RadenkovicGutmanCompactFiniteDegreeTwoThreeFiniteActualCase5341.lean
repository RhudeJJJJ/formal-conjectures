/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5341 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap5341 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5341 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5341_checked : acceptsGraphIso
    (source (graph core5341) (root 6) 3 4) DegreeTwoThreeSpectrum4628.graph sourceMap5341=true := by decide +kernel
theorem fusedMap5341_checked : acceptsGraphIso
    (fused (graph core5341) (root 6) 3 4) DegreeTwoThreeSpectrum3907.graph fusedMap5341=true := by decide +kernel
theorem certified5341 : Certified (graph core5341) (root 6) 3 4 :=
  of_native_maps core5341 DegreeTwoThreeSpectrum4628.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap5341 fusedMap5341 sourceMap5341_checked fusedMap5341_checked
    DegreeTwoThreeFiniteComparisons.comparison5341
#print axioms sourceMap5341_checked
#print axioms fusedMap5341_checked
#print axioms certified5341
def sourceMap5341swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5341swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5341swap_checked : acceptsGraphIso
    (source (graph core5341) (root 6) 4 3) DegreeTwoThreeSpectrum4628.graph sourceMap5341swap=true := by decide +kernel
theorem fusedMap5341swap_checked : acceptsGraphIso
    (fused (graph core5341) (root 6) 4 3) DegreeTwoThreeSpectrum3907.graph fusedMap5341swap=true := by decide +kernel
theorem certified5341swap : Certified (graph core5341) (root 6) 4 3 :=
  of_native_maps core5341 DegreeTwoThreeSpectrum4628.graph DegreeTwoThreeSpectrum3907.graph
    sourceMap5341swap fusedMap5341swap sourceMap5341swap_checked fusedMap5341swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5341
#print axioms sourceMap5341swap_checked
#print axioms fusedMap5341swap_checked
#print axioms certified5341swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
