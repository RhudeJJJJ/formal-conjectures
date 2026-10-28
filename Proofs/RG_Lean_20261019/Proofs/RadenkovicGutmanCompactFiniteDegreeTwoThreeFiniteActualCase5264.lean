/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5264 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap5264 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5264 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5264_checked : acceptsGraphIso
    (source (graph core5264) (root 7) 2 5) DegreeTwoThreeSpectrum6215.graph sourceMap5264=true := by decide +kernel
theorem fusedMap5264_checked : acceptsGraphIso
    (fused (graph core5264) (root 7) 2 5) DegreeTwoThreeSpectrum5237.graph fusedMap5264=true := by decide +kernel
theorem certified5264 : Certified (graph core5264) (root 7) 2 5 :=
  of_native_maps core5264 DegreeTwoThreeSpectrum6215.graph DegreeTwoThreeSpectrum5237.graph
    sourceMap5264 fusedMap5264 sourceMap5264_checked fusedMap5264_checked
    DegreeTwoThreeFiniteComparisons.comparison5264
#print axioms sourceMap5264_checked
#print axioms fusedMap5264_checked
#print axioms certified5264
def sourceMap5264swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5264swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5264swap_checked : acceptsGraphIso
    (source (graph core5264) (root 7) 5 2) DegreeTwoThreeSpectrum6215.graph sourceMap5264swap=true := by decide +kernel
theorem fusedMap5264swap_checked : acceptsGraphIso
    (fused (graph core5264) (root 7) 5 2) DegreeTwoThreeSpectrum5237.graph fusedMap5264swap=true := by decide +kernel
theorem certified5264swap : Certified (graph core5264) (root 7) 5 2 :=
  of_native_maps core5264 DegreeTwoThreeSpectrum6215.graph DegreeTwoThreeSpectrum5237.graph
    sourceMap5264swap fusedMap5264swap sourceMap5264swap_checked fusedMap5264swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5264
#print axioms sourceMap5264swap_checked
#print axioms fusedMap5264swap_checked
#print axioms certified5264swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
