/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5265 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap5265 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5265 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5265_checked : acceptsGraphIso
    (source (graph core5265) (root 7) 2 5) DegreeTwoThreeSpectrum6256.graph sourceMap5265=true := by decide +kernel
theorem fusedMap5265_checked : acceptsGraphIso
    (fused (graph core5265) (root 7) 2 5) DegreeTwoThreeSpectrum5254.graph fusedMap5265=true := by decide +kernel
theorem certified5265 : Certified (graph core5265) (root 7) 2 5 :=
  of_native_maps core5265 DegreeTwoThreeSpectrum6256.graph DegreeTwoThreeSpectrum5254.graph
    sourceMap5265 fusedMap5265 sourceMap5265_checked fusedMap5265_checked
    DegreeTwoThreeFiniteComparisons.comparison5265
#print axioms sourceMap5265_checked
#print axioms fusedMap5265_checked
#print axioms certified5265
def sourceMap5265swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5265swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5265swap_checked : acceptsGraphIso
    (source (graph core5265) (root 7) 5 2) DegreeTwoThreeSpectrum6256.graph sourceMap5265swap=true := by decide +kernel
theorem fusedMap5265swap_checked : acceptsGraphIso
    (fused (graph core5265) (root 7) 5 2) DegreeTwoThreeSpectrum5254.graph fusedMap5265swap=true := by decide +kernel
theorem certified5265swap : Certified (graph core5265) (root 7) 5 2 :=
  of_native_maps core5265 DegreeTwoThreeSpectrum6256.graph DegreeTwoThreeSpectrum5254.graph
    sourceMap5265swap fusedMap5265swap sourceMap5265swap_checked fusedMap5265swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5265
#print axioms sourceMap5265swap_checked
#print axioms fusedMap5265swap_checked
#print axioms certified5265swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
