/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5175 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap5175 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5175 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5175_checked : acceptsGraphIso
    (source (graph core5175) (root 8) 2 4) DegreeTwoThreeSpectrum6973.graph sourceMap5175=true := by decide +kernel
theorem fusedMap5175_checked : acceptsGraphIso
    (fused (graph core5175) (root 8) 2 4) DegreeTwoThreeSpectrum5765.graph fusedMap5175=true := by decide +kernel
theorem certified5175 : Certified (graph core5175) (root 8) 2 4 :=
  of_native_maps core5175 DegreeTwoThreeSpectrum6973.graph DegreeTwoThreeSpectrum5765.graph
    sourceMap5175 fusedMap5175 sourceMap5175_checked fusedMap5175_checked
    DegreeTwoThreeFiniteComparisons.comparison5175
#print axioms sourceMap5175_checked
#print axioms fusedMap5175_checked
#print axioms certified5175
def sourceMap5175swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5175swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5175swap_checked : acceptsGraphIso
    (source (graph core5175) (root 8) 4 2) DegreeTwoThreeSpectrum6973.graph sourceMap5175swap=true := by decide +kernel
theorem fusedMap5175swap_checked : acceptsGraphIso
    (fused (graph core5175) (root 8) 4 2) DegreeTwoThreeSpectrum5765.graph fusedMap5175swap=true := by decide +kernel
theorem certified5175swap : Certified (graph core5175) (root 8) 4 2 :=
  of_native_maps core5175 DegreeTwoThreeSpectrum6973.graph DegreeTwoThreeSpectrum5765.graph
    sourceMap5175swap fusedMap5175swap sourceMap5175swap_checked fusedMap5175swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5175
#print axioms sourceMap5175swap_checked
#print axioms fusedMap5175swap_checked
#print axioms certified5175swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
