/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5351 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap5351 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5351 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5351_checked : acceptsGraphIso
    (source (graph core5351) (root 6) 3 4) DegreeTwoThreeSpectrum4648.graph sourceMap5351=true := by decide +kernel
theorem fusedMap5351_checked : acceptsGraphIso
    (fused (graph core5351) (root 6) 3 4) DegreeTwoThreeSpectrum3917.graph fusedMap5351=true := by decide +kernel
theorem certified5351 : Certified (graph core5351) (root 6) 3 4 :=
  of_native_maps core5351 DegreeTwoThreeSpectrum4648.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap5351 fusedMap5351 sourceMap5351_checked fusedMap5351_checked
    DegreeTwoThreeFiniteComparisons.comparison5351
#print axioms sourceMap5351_checked
#print axioms fusedMap5351_checked
#print axioms certified5351
def sourceMap5351swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5351swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5351swap_checked : acceptsGraphIso
    (source (graph core5351) (root 6) 4 3) DegreeTwoThreeSpectrum4648.graph sourceMap5351swap=true := by decide +kernel
theorem fusedMap5351swap_checked : acceptsGraphIso
    (fused (graph core5351) (root 6) 4 3) DegreeTwoThreeSpectrum3917.graph fusedMap5351swap=true := by decide +kernel
theorem certified5351swap : Certified (graph core5351) (root 6) 4 3 :=
  of_native_maps core5351 DegreeTwoThreeSpectrum4648.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap5351swap fusedMap5351swap sourceMap5351swap_checked fusedMap5351swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5351
#print axioms sourceMap5351swap_checked
#print axioms fusedMap5351swap_checked
#print axioms certified5351swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
