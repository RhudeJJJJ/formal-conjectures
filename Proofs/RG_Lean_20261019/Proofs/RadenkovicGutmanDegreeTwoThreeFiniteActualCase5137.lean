/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5137 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap5137 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5137 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5137_checked : acceptsGraphIso
    (source (graph core5137) (root 8) 2 4) DegreeTwoThreeSpectrum6958.graph sourceMap5137=true := by decide +kernel
theorem fusedMap5137_checked : acceptsGraphIso
    (fused (graph core5137) (root 8) 2 4) DegreeTwoThreeSpectrum5057.graph fusedMap5137=true := by decide +kernel
theorem certified5137 : Certified (graph core5137) (root 8) 2 4 :=
  of_native_maps core5137 DegreeTwoThreeSpectrum6958.graph DegreeTwoThreeSpectrum5057.graph
    sourceMap5137 fusedMap5137 sourceMap5137_checked fusedMap5137_checked
    DegreeTwoThreeFiniteComparisons.comparison5137
#print axioms sourceMap5137_checked
#print axioms fusedMap5137_checked
#print axioms certified5137
def sourceMap5137swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5137swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5137swap_checked : acceptsGraphIso
    (source (graph core5137) (root 8) 4 2) DegreeTwoThreeSpectrum6958.graph sourceMap5137swap=true := by decide +kernel
theorem fusedMap5137swap_checked : acceptsGraphIso
    (fused (graph core5137) (root 8) 4 2) DegreeTwoThreeSpectrum5057.graph fusedMap5137swap=true := by decide +kernel
theorem certified5137swap : Certified (graph core5137) (root 8) 4 2 :=
  of_native_maps core5137 DegreeTwoThreeSpectrum6958.graph DegreeTwoThreeSpectrum5057.graph
    sourceMap5137swap fusedMap5137swap sourceMap5137swap_checked fusedMap5137swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5137
#print axioms sourceMap5137swap_checked
#print axioms fusedMap5137swap_checked
#print axioms certified5137swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
