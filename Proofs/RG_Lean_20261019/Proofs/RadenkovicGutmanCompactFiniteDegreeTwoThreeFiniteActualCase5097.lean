/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5097 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap5097 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5097 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5097_checked : acceptsGraphIso
    (source (graph core5097) (root 7) 2 4) DegreeTwoThreeSpectrum4599.graph sourceMap5097=true := by decide +kernel
theorem fusedMap5097_checked : acceptsGraphIso
    (fused (graph core5097) (root 7) 2 4) DegreeTwoThreeSpectrum4086.graph fusedMap5097=true := by decide +kernel
theorem certified5097 : Certified (graph core5097) (root 7) 2 4 :=
  of_native_maps core5097 DegreeTwoThreeSpectrum4599.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap5097 fusedMap5097 sourceMap5097_checked fusedMap5097_checked
    DegreeTwoThreeFiniteComparisons.comparison5097
#print axioms sourceMap5097_checked
#print axioms fusedMap5097_checked
#print axioms certified5097
def sourceMap5097swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5097swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5097swap_checked : acceptsGraphIso
    (source (graph core5097) (root 7) 4 2) DegreeTwoThreeSpectrum4599.graph sourceMap5097swap=true := by decide +kernel
theorem fusedMap5097swap_checked : acceptsGraphIso
    (fused (graph core5097) (root 7) 4 2) DegreeTwoThreeSpectrum4086.graph fusedMap5097swap=true := by decide +kernel
theorem certified5097swap : Certified (graph core5097) (root 7) 4 2 :=
  of_native_maps core5097 DegreeTwoThreeSpectrum4599.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap5097swap fusedMap5097swap sourceMap5097swap_checked fusedMap5097swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5097
#print axioms sourceMap5097swap_checked
#print axioms fusedMap5097swap_checked
#print axioms certified5097swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
