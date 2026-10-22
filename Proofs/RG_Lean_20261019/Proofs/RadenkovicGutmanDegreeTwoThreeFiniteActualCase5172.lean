/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5172 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap5172 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5172 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5172_checked : acceptsGraphIso
    (source (graph core5172) (root 8) 2 4) DegreeTwoThreeSpectrum6921.graph sourceMap5172=true := by decide +kernel
theorem fusedMap5172_checked : acceptsGraphIso
    (fused (graph core5172) (root 8) 2 4) DegreeTwoThreeSpectrum5707.graph fusedMap5172=true := by decide +kernel
theorem certified5172 : Certified (graph core5172) (root 8) 2 4 :=
  of_native_maps core5172 DegreeTwoThreeSpectrum6921.graph DegreeTwoThreeSpectrum5707.graph
    sourceMap5172 fusedMap5172 sourceMap5172_checked fusedMap5172_checked
    DegreeTwoThreeFiniteComparisons.comparison5172
#print axioms sourceMap5172_checked
#print axioms fusedMap5172_checked
#print axioms certified5172
def sourceMap5172swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5172swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5172swap_checked : acceptsGraphIso
    (source (graph core5172) (root 8) 4 2) DegreeTwoThreeSpectrum6921.graph sourceMap5172swap=true := by decide +kernel
theorem fusedMap5172swap_checked : acceptsGraphIso
    (fused (graph core5172) (root 8) 4 2) DegreeTwoThreeSpectrum5707.graph fusedMap5172swap=true := by decide +kernel
theorem certified5172swap : Certified (graph core5172) (root 8) 4 2 :=
  of_native_maps core5172 DegreeTwoThreeSpectrum6921.graph DegreeTwoThreeSpectrum5707.graph
    sourceMap5172swap fusedMap5172swap sourceMap5172swap_checked fusedMap5172swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5172
#print axioms sourceMap5172swap_checked
#print axioms fusedMap5172swap_checked
#print axioms certified5172swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
