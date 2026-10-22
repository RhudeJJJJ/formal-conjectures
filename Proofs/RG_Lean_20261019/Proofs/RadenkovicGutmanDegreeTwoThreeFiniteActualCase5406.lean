/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5406 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5406 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5,11,12,13,14,15,16] (sourceLabel 5 4 5 v)
def fusedMap5406 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 4 5 v)
theorem sourceMap5406_checked : acceptsGraphIso
    (source (graph core5406) (root 5) 4 5) DegreeTwoThreeSpectrum5923.graph sourceMap5406=true := by decide +kernel
theorem fusedMap5406_checked : acceptsGraphIso
    (fused (graph core5406) (root 5) 4 5) DegreeTwoThreeSpectrum5055.graph fusedMap5406=true := by decide +kernel
theorem certified5406 : Certified (graph core5406) (root 5) 4 5 :=
  of_native_maps core5406 DegreeTwoThreeSpectrum5923.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap5406 fusedMap5406 sourceMap5406_checked fusedMap5406_checked
    DegreeTwoThreeFiniteComparisons.comparison5406
#print axioms sourceMap5406_checked
#print axioms fusedMap5406_checked
#print axioms certified5406
def sourceMap5406swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5] (sourceLabel 5 5 4 v)
def fusedMap5406swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 5 4 v)
theorem sourceMap5406swap_checked : acceptsGraphIso
    (source (graph core5406) (root 5) 5 4) DegreeTwoThreeSpectrum5923.graph sourceMap5406swap=true := by decide +kernel
theorem fusedMap5406swap_checked : acceptsGraphIso
    (fused (graph core5406) (root 5) 5 4) DegreeTwoThreeSpectrum5055.graph fusedMap5406swap=true := by decide +kernel
theorem certified5406swap : Certified (graph core5406) (root 5) 5 4 :=
  of_native_maps core5406 DegreeTwoThreeSpectrum5923.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap5406swap fusedMap5406swap sourceMap5406swap_checked fusedMap5406swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5406
#print axioms sourceMap5406swap_checked
#print axioms fusedMap5406swap_checked
#print axioms certified5406swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
