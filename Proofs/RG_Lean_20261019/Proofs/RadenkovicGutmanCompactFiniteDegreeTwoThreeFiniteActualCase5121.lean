/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5121 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap5121 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5121 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5121_checked : acceptsGraphIso
    (source (graph core5121) (root 8) 2 4) DegreeTwoThreeSpectrum5648.graph sourceMap5121=true := by decide +kernel
theorem fusedMap5121_checked : acceptsGraphIso
    (fused (graph core5121) (root 8) 2 4) DegreeTwoThreeSpectrum5042.graph fusedMap5121=true := by decide +kernel
theorem certified5121 : Certified (graph core5121) (root 8) 2 4 :=
  of_native_maps core5121 DegreeTwoThreeSpectrum5648.graph DegreeTwoThreeSpectrum5042.graph
    sourceMap5121 fusedMap5121 sourceMap5121_checked fusedMap5121_checked
    DegreeTwoThreeFiniteComparisons.comparison5121
#print axioms sourceMap5121_checked
#print axioms fusedMap5121_checked
#print axioms certified5121
def sourceMap5121swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5121swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5121swap_checked : acceptsGraphIso
    (source (graph core5121) (root 8) 4 2) DegreeTwoThreeSpectrum5648.graph sourceMap5121swap=true := by decide +kernel
theorem fusedMap5121swap_checked : acceptsGraphIso
    (fused (graph core5121) (root 8) 4 2) DegreeTwoThreeSpectrum5042.graph fusedMap5121swap=true := by decide +kernel
theorem certified5121swap : Certified (graph core5121) (root 8) 4 2 :=
  of_native_maps core5121 DegreeTwoThreeSpectrum5648.graph DegreeTwoThreeSpectrum5042.graph
    sourceMap5121swap fusedMap5121swap sourceMap5121swap_checked fusedMap5121swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5121
#print axioms sourceMap5121swap_checked
#print axioms fusedMap5121swap_checked
#print axioms certified5121swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
