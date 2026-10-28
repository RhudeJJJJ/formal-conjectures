/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5089 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap5089 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5089 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5089_checked : acceptsGraphIso
    (source (graph core5089) (root 7) 2 4) DegreeTwoThreeSpectrum4320.graph sourceMap5089=true := by decide +kernel
theorem fusedMap5089_checked : acceptsGraphIso
    (fused (graph core5089) (root 7) 2 4) DegreeTwoThreeSpectrum3935.graph fusedMap5089=true := by decide +kernel
theorem certified5089 : Certified (graph core5089) (root 7) 2 4 :=
  of_native_maps core5089 DegreeTwoThreeSpectrum4320.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap5089 fusedMap5089 sourceMap5089_checked fusedMap5089_checked
    DegreeTwoThreeFiniteComparisons.comparison5089
#print axioms sourceMap5089_checked
#print axioms fusedMap5089_checked
#print axioms certified5089
def sourceMap5089swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5089swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5089swap_checked : acceptsGraphIso
    (source (graph core5089) (root 7) 4 2) DegreeTwoThreeSpectrum4320.graph sourceMap5089swap=true := by decide +kernel
theorem fusedMap5089swap_checked : acceptsGraphIso
    (fused (graph core5089) (root 7) 4 2) DegreeTwoThreeSpectrum3935.graph fusedMap5089swap=true := by decide +kernel
theorem certified5089swap : Certified (graph core5089) (root 7) 4 2 :=
  of_native_maps core5089 DegreeTwoThreeSpectrum4320.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap5089swap fusedMap5089swap sourceMap5089swap_checked fusedMap5089swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5089
#print axioms sourceMap5089swap_checked
#print axioms fusedMap5089swap_checked
#print axioms certified5089swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
