/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5099 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap5099 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5099 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5099_checked : acceptsGraphIso
    (source (graph core5099) (root 7) 2 4) DegreeTwoThreeSpectrum4640.graph sourceMap5099=true := by decide +kernel
theorem fusedMap5099_checked : acceptsGraphIso
    (fused (graph core5099) (root 7) 2 4) DegreeTwoThreeSpectrum4120.graph fusedMap5099=true := by decide +kernel
theorem certified5099 : Certified (graph core5099) (root 7) 2 4 :=
  of_native_maps core5099 DegreeTwoThreeSpectrum4640.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap5099 fusedMap5099 sourceMap5099_checked fusedMap5099_checked
    DegreeTwoThreeFiniteComparisons.comparison5099
#print axioms sourceMap5099_checked
#print axioms fusedMap5099_checked
#print axioms certified5099
def sourceMap5099swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5099swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5099swap_checked : acceptsGraphIso
    (source (graph core5099) (root 7) 4 2) DegreeTwoThreeSpectrum4640.graph sourceMap5099swap=true := by decide +kernel
theorem fusedMap5099swap_checked : acceptsGraphIso
    (fused (graph core5099) (root 7) 4 2) DegreeTwoThreeSpectrum4120.graph fusedMap5099swap=true := by decide +kernel
theorem certified5099swap : Certified (graph core5099) (root 7) 4 2 :=
  of_native_maps core5099 DegreeTwoThreeSpectrum4640.graph DegreeTwoThreeSpectrum4120.graph
    sourceMap5099swap fusedMap5099swap sourceMap5099swap_checked fusedMap5099swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5099
#print axioms sourceMap5099swap_checked
#print axioms fusedMap5099swap_checked
#print axioms certified5099swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
