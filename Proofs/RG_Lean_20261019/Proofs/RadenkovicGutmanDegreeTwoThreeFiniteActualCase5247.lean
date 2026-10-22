/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5247 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap5247 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5247 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5247_checked : acceptsGraphIso
    (source (graph core5247) (root 7) 2 5) DegreeTwoThreeSpectrum5923.graph sourceMap5247=true := by decide +kernel
theorem fusedMap5247_checked : acceptsGraphIso
    (fused (graph core5247) (root 7) 2 5) DegreeTwoThreeSpectrum5111.graph fusedMap5247=true := by decide +kernel
theorem certified5247 : Certified (graph core5247) (root 7) 2 5 :=
  of_native_maps core5247 DegreeTwoThreeSpectrum5923.graph DegreeTwoThreeSpectrum5111.graph
    sourceMap5247 fusedMap5247 sourceMap5247_checked fusedMap5247_checked
    DegreeTwoThreeFiniteComparisons.comparison5247
#print axioms sourceMap5247_checked
#print axioms fusedMap5247_checked
#print axioms certified5247
def sourceMap5247swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,16,6,7,8] (sourceLabel 7 5 2 v)
def fusedMap5247swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5247swap_checked : acceptsGraphIso
    (source (graph core5247) (root 7) 5 2) DegreeTwoThreeSpectrum5923.graph sourceMap5247swap=true := by decide +kernel
theorem fusedMap5247swap_checked : acceptsGraphIso
    (fused (graph core5247) (root 7) 5 2) DegreeTwoThreeSpectrum5111.graph fusedMap5247swap=true := by decide +kernel
theorem certified5247swap : Certified (graph core5247) (root 7) 5 2 :=
  of_native_maps core5247 DegreeTwoThreeSpectrum5923.graph DegreeTwoThreeSpectrum5111.graph
    sourceMap5247swap fusedMap5247swap sourceMap5247swap_checked fusedMap5247swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5247
#print axioms sourceMap5247swap_checked
#print axioms fusedMap5247swap_checked
#print axioms certified5247swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
