/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5405 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5405 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5,11,12,13,14,15,16] (sourceLabel 5 4 5 v)
def fusedMap5405 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 4 5 v)
theorem sourceMap5405_checked : acceptsGraphIso
    (source (graph core5405) (root 5) 4 5) DegreeTwoThreeSpectrum5921.graph sourceMap5405=true := by decide +kernel
theorem fusedMap5405_checked : acceptsGraphIso
    (fused (graph core5405) (root 5) 4 5) DegreeTwoThreeSpectrum5027.graph fusedMap5405=true := by decide +kernel
theorem certified5405 : Certified (graph core5405) (root 5) 4 5 :=
  of_native_maps core5405 DegreeTwoThreeSpectrum5921.graph DegreeTwoThreeSpectrum5027.graph
    sourceMap5405 fusedMap5405 sourceMap5405_checked fusedMap5405_checked
    DegreeTwoThreeFiniteComparisons.comparison5405
#print axioms sourceMap5405_checked
#print axioms fusedMap5405_checked
#print axioms certified5405
def sourceMap5405swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5] (sourceLabel 5 5 4 v)
def fusedMap5405swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 5 4 v)
theorem sourceMap5405swap_checked : acceptsGraphIso
    (source (graph core5405) (root 5) 5 4) DegreeTwoThreeSpectrum5921.graph sourceMap5405swap=true := by decide +kernel
theorem fusedMap5405swap_checked : acceptsGraphIso
    (fused (graph core5405) (root 5) 5 4) DegreeTwoThreeSpectrum5027.graph fusedMap5405swap=true := by decide +kernel
theorem certified5405swap : Certified (graph core5405) (root 5) 5 4 :=
  of_native_maps core5405 DegreeTwoThreeSpectrum5921.graph DegreeTwoThreeSpectrum5027.graph
    sourceMap5405swap fusedMap5405swap sourceMap5405swap_checked fusedMap5405swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5405
#print axioms sourceMap5405swap_checked
#print axioms fusedMap5405swap_checked
#print axioms certified5405swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
