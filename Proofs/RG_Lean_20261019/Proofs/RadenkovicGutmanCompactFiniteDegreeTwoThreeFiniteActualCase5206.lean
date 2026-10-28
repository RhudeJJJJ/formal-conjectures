/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5206 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap5206 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5206 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5206_checked : acceptsGraphIso
    (source (graph core5206) (root 8) 2 4) DegreeTwoThreeSpectrum7401.graph sourceMap5206=true := by decide +kernel
theorem fusedMap5206_checked : acceptsGraphIso
    (fused (graph core5206) (root 8) 2 4) DegreeTwoThreeSpectrum5499.graph fusedMap5206=true := by decide +kernel
theorem certified5206 : Certified (graph core5206) (root 8) 2 4 :=
  of_native_maps core5206 DegreeTwoThreeSpectrum7401.graph DegreeTwoThreeSpectrum5499.graph
    sourceMap5206 fusedMap5206 sourceMap5206_checked fusedMap5206_checked
    DegreeTwoThreeFiniteComparisons.comparison5206
#print axioms sourceMap5206_checked
#print axioms fusedMap5206_checked
#print axioms certified5206
def sourceMap5206swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5206swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5206swap_checked : acceptsGraphIso
    (source (graph core5206) (root 8) 4 2) DegreeTwoThreeSpectrum7401.graph sourceMap5206swap=true := by decide +kernel
theorem fusedMap5206swap_checked : acceptsGraphIso
    (fused (graph core5206) (root 8) 4 2) DegreeTwoThreeSpectrum5499.graph fusedMap5206swap=true := by decide +kernel
theorem certified5206swap : Certified (graph core5206) (root 8) 4 2 :=
  of_native_maps core5206 DegreeTwoThreeSpectrum7401.graph DegreeTwoThreeSpectrum5499.graph
    sourceMap5206swap fusedMap5206swap sourceMap5206swap_checked fusedMap5206swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5206
#print axioms sourceMap5206swap_checked
#print axioms fusedMap5206swap_checked
#print axioms certified5206swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
