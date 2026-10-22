/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5340 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap5340 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5340 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5340_checked : acceptsGraphIso
    (source (graph core5340) (root 6) 3 4) DegreeTwoThreeSpectrum4626.graph sourceMap5340=true := by decide +kernel
theorem fusedMap5340_checked : acceptsGraphIso
    (fused (graph core5340) (root 6) 3 4) DegreeTwoThreeSpectrum3877.graph fusedMap5340=true := by decide +kernel
theorem certified5340 : Certified (graph core5340) (root 6) 3 4 :=
  of_native_maps core5340 DegreeTwoThreeSpectrum4626.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap5340 fusedMap5340 sourceMap5340_checked fusedMap5340_checked
    DegreeTwoThreeFiniteComparisons.comparison5340
#print axioms sourceMap5340_checked
#print axioms fusedMap5340_checked
#print axioms certified5340
def sourceMap5340swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,15,5,6,7,8] (sourceLabel 6 4 3 v)
def fusedMap5340swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5340swap_checked : acceptsGraphIso
    (source (graph core5340) (root 6) 4 3) DegreeTwoThreeSpectrum4626.graph sourceMap5340swap=true := by decide +kernel
theorem fusedMap5340swap_checked : acceptsGraphIso
    (fused (graph core5340) (root 6) 4 3) DegreeTwoThreeSpectrum3877.graph fusedMap5340swap=true := by decide +kernel
theorem certified5340swap : Certified (graph core5340) (root 6) 4 3 :=
  of_native_maps core5340 DegreeTwoThreeSpectrum4626.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap5340swap fusedMap5340swap sourceMap5340swap_checked fusedMap5340swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5340
#print axioms sourceMap5340swap_checked
#print axioms fusedMap5340swap_checked
#print axioms certified5340swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
