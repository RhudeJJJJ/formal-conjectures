/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2417 : Family 9 := level9.get ⟨587,by decide⟩
def sourceMap2417 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2417 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2417_checked : acceptsGraphIso
    (source (graph core2417) (root 9) 0 4) DegreeTwoThreeSpectrum4722.graph sourceMap2417=true := by decide +kernel
theorem fusedMap2417_checked : acceptsGraphIso
    (fused (graph core2417) (root 9) 0 4) DegreeTwoThreeSpectrum4260.graph fusedMap2417=true := by decide +kernel
theorem certified2417 : Certified (graph core2417) (root 9) 0 4 :=
  of_native_maps core2417 DegreeTwoThreeSpectrum4722.graph DegreeTwoThreeSpectrum4260.graph
    sourceMap2417 fusedMap2417 sourceMap2417_checked fusedMap2417_checked
    DegreeTwoThreeFiniteComparisons.comparison2417
#print axioms sourceMap2417_checked
#print axioms fusedMap2417_checked
#print axioms certified2417
def sourceMap2417swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2417swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2417swap_checked : acceptsGraphIso
    (source (graph core2417) (root 9) 4 0) DegreeTwoThreeSpectrum4722.graph sourceMap2417swap=true := by decide +kernel
theorem fusedMap2417swap_checked : acceptsGraphIso
    (fused (graph core2417) (root 9) 4 0) DegreeTwoThreeSpectrum4260.graph fusedMap2417swap=true := by decide +kernel
theorem certified2417swap : Certified (graph core2417) (root 9) 4 0 :=
  of_native_maps core2417 DegreeTwoThreeSpectrum4722.graph DegreeTwoThreeSpectrum4260.graph
    sourceMap2417swap fusedMap2417swap sourceMap2417swap_checked fusedMap2417swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2417
#print axioms sourceMap2417swap_checked
#print axioms fusedMap2417swap_checked
#print axioms certified2417swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
