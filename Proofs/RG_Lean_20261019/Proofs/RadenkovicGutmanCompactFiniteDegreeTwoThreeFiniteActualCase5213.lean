/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5213 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap5213 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,2,3,4,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5213 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5213_checked : acceptsGraphIso
    (source (graph core5213) (root 8) 2 4) DegreeTwoThreeSpectrum7555.graph sourceMap5213=true := by decide +kernel
theorem fusedMap5213_checked : acceptsGraphIso
    (fused (graph core5213) (root 8) 2 4) DegreeTwoThreeSpectrum5996.graph fusedMap5213=true := by decide +kernel
theorem certified5213 : Certified (graph core5213) (root 8) 2 4 :=
  of_native_maps core5213 DegreeTwoThreeSpectrum7555.graph DegreeTwoThreeSpectrum5996.graph
    sourceMap5213 fusedMap5213 sourceMap5213_checked fusedMap5213_checked
    DegreeTwoThreeFiniteComparisons.comparison5213
#print axioms sourceMap5213_checked
#print axioms fusedMap5213_checked
#print axioms certified5213
def sourceMap5213swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,0,13,14,15,16,2,3,4] (sourceLabel 8 4 2 v)
def fusedMap5213swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5213swap_checked : acceptsGraphIso
    (source (graph core5213) (root 8) 4 2) DegreeTwoThreeSpectrum7555.graph sourceMap5213swap=true := by decide +kernel
theorem fusedMap5213swap_checked : acceptsGraphIso
    (fused (graph core5213) (root 8) 4 2) DegreeTwoThreeSpectrum5996.graph fusedMap5213swap=true := by decide +kernel
theorem certified5213swap : Certified (graph core5213) (root 8) 4 2 :=
  of_native_maps core5213 DegreeTwoThreeSpectrum7555.graph DegreeTwoThreeSpectrum5996.graph
    sourceMap5213swap fusedMap5213swap sourceMap5213swap_checked fusedMap5213swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5213
#print axioms sourceMap5213swap_checked
#print axioms fusedMap5213swap_checked
#print axioms certified5213swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
