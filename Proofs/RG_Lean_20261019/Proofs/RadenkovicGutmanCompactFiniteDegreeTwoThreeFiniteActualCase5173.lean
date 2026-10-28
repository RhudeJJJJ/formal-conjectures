/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5173 : Family 8 := level8.get ⟨172,by decide⟩
def sourceMap5173 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5173 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5173_checked : acceptsGraphIso
    (source (graph core5173) (root 8) 2 4) DegreeTwoThreeSpectrum6937.graph sourceMap5173=true := by decide +kernel
theorem fusedMap5173_checked : acceptsGraphIso
    (fused (graph core5173) (root 8) 2 4) DegreeTwoThreeSpectrum5731.graph fusedMap5173=true := by decide +kernel
theorem certified5173 : Certified (graph core5173) (root 8) 2 4 :=
  of_native_maps core5173 DegreeTwoThreeSpectrum6937.graph DegreeTwoThreeSpectrum5731.graph
    sourceMap5173 fusedMap5173 sourceMap5173_checked fusedMap5173_checked
    DegreeTwoThreeFiniteComparisons.comparison5173
#print axioms sourceMap5173_checked
#print axioms fusedMap5173_checked
#print axioms certified5173
def sourceMap5173swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5173swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5173swap_checked : acceptsGraphIso
    (source (graph core5173) (root 8) 4 2) DegreeTwoThreeSpectrum6937.graph sourceMap5173swap=true := by decide +kernel
theorem fusedMap5173swap_checked : acceptsGraphIso
    (fused (graph core5173) (root 8) 4 2) DegreeTwoThreeSpectrum5731.graph fusedMap5173swap=true := by decide +kernel
theorem certified5173swap : Certified (graph core5173) (root 8) 4 2 :=
  of_native_maps core5173 DegreeTwoThreeSpectrum6937.graph DegreeTwoThreeSpectrum5731.graph
    sourceMap5173swap fusedMap5173swap sourceMap5173swap_checked fusedMap5173swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5173
#print axioms sourceMap5173swap_checked
#print axioms fusedMap5173swap_checked
#print axioms certified5173swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
