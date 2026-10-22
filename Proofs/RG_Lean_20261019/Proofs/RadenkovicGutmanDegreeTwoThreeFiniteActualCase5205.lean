/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5205 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap5205 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,8,9,10,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5205 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5205_checked : acceptsGraphIso
    (source (graph core5205) (root 8) 2 4) DegreeTwoThreeSpectrum7388.graph sourceMap5205=true := by decide +kernel
theorem fusedMap5205_checked : acceptsGraphIso
    (fused (graph core5205) (root 8) 2 4) DegreeTwoThreeSpectrum5485.graph fusedMap5205=true := by decide +kernel
theorem certified5205 : Certified (graph core5205) (root 8) 2 4 :=
  of_native_maps core5205 DegreeTwoThreeSpectrum7388.graph DegreeTwoThreeSpectrum5485.graph
    sourceMap5205 fusedMap5205 sourceMap5205_checked fusedMap5205_checked
    DegreeTwoThreeFiniteComparisons.comparison5205
#print axioms sourceMap5205_checked
#print axioms fusedMap5205_checked
#print axioms certified5205
def sourceMap5205swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,0,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5205swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5205swap_checked : acceptsGraphIso
    (source (graph core5205) (root 8) 4 2) DegreeTwoThreeSpectrum7388.graph sourceMap5205swap=true := by decide +kernel
theorem fusedMap5205swap_checked : acceptsGraphIso
    (fused (graph core5205) (root 8) 4 2) DegreeTwoThreeSpectrum5485.graph fusedMap5205swap=true := by decide +kernel
theorem certified5205swap : Certified (graph core5205) (root 8) 4 2 :=
  of_native_maps core5205 DegreeTwoThreeSpectrum7388.graph DegreeTwoThreeSpectrum5485.graph
    sourceMap5205swap fusedMap5205swap sourceMap5205swap_checked fusedMap5205swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5205
#print axioms sourceMap5205swap_checked
#print axioms fusedMap5205swap_checked
#print axioms certified5205swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
