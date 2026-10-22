/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3172 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap3172 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3172 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3172_checked : acceptsGraphIso
    (source (graph core3172) (root 8) 0 5) DegreeTwoThreeSpectrum4318.graph sourceMap3172=true := by decide +kernel
theorem fusedMap3172_checked : acceptsGraphIso
    (fused (graph core3172) (root 8) 0 5) DegreeTwoThreeSpectrum3929.graph fusedMap3172=true := by decide +kernel
theorem certified3172 : Certified (graph core3172) (root 8) 0 5 :=
  of_native_maps core3172 DegreeTwoThreeSpectrum4318.graph DegreeTwoThreeSpectrum3929.graph
    sourceMap3172 fusedMap3172 sourceMap3172_checked fusedMap3172_checked
    DegreeTwoThreeFiniteComparisons.comparison3172
#print axioms sourceMap3172_checked
#print axioms fusedMap3172_checked
#print axioms certified3172
def sourceMap3172swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3172swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3172swap_checked : acceptsGraphIso
    (source (graph core3172) (root 8) 5 0) DegreeTwoThreeSpectrum4318.graph sourceMap3172swap=true := by decide +kernel
theorem fusedMap3172swap_checked : acceptsGraphIso
    (fused (graph core3172) (root 8) 5 0) DegreeTwoThreeSpectrum3929.graph fusedMap3172swap=true := by decide +kernel
theorem certified3172swap : Certified (graph core3172) (root 8) 5 0 :=
  of_native_maps core3172 DegreeTwoThreeSpectrum4318.graph DegreeTwoThreeSpectrum3929.graph
    sourceMap3172swap fusedMap3172swap sourceMap3172swap_checked fusedMap3172swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3172
#print axioms sourceMap3172swap_checked
#print axioms fusedMap3172swap_checked
#print axioms certified3172swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
