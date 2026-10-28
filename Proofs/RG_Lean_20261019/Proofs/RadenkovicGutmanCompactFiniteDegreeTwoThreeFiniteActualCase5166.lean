/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5166 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap5166 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5166 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5166_checked : acceptsGraphIso
    (source (graph core5166) (root 8) 2 4) DegreeTwoThreeSpectrum6733.graph sourceMap5166=true := by decide +kernel
theorem fusedMap5166_checked : acceptsGraphIso
    (fused (graph core5166) (root 8) 2 4) DegreeTwoThreeSpectrum5577.graph fusedMap5166=true := by decide +kernel
theorem certified5166 : Certified (graph core5166) (root 8) 2 4 :=
  of_native_maps core5166 DegreeTwoThreeSpectrum6733.graph DegreeTwoThreeSpectrum5577.graph
    sourceMap5166 fusedMap5166 sourceMap5166_checked fusedMap5166_checked
    DegreeTwoThreeFiniteComparisons.comparison5166
#print axioms sourceMap5166_checked
#print axioms fusedMap5166_checked
#print axioms certified5166
def sourceMap5166swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5166swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5166swap_checked : acceptsGraphIso
    (source (graph core5166) (root 8) 4 2) DegreeTwoThreeSpectrum6733.graph sourceMap5166swap=true := by decide +kernel
theorem fusedMap5166swap_checked : acceptsGraphIso
    (fused (graph core5166) (root 8) 4 2) DegreeTwoThreeSpectrum5577.graph fusedMap5166swap=true := by decide +kernel
theorem certified5166swap : Certified (graph core5166) (root 8) 4 2 :=
  of_native_maps core5166 DegreeTwoThreeSpectrum6733.graph DegreeTwoThreeSpectrum5577.graph
    sourceMap5166swap fusedMap5166swap sourceMap5166swap_checked fusedMap5166swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5166
#print axioms sourceMap5166swap_checked
#print axioms fusedMap5166swap_checked
#print axioms certified5166swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
