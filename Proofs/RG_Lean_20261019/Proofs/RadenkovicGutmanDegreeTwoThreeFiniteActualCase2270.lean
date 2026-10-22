/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2270 : Family 9 := level9.get ⟨210,by decide⟩
def sourceMap2270 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2270 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2270_checked : acceptsGraphIso
    (source (graph core2270) (root 9) 0 4) DegreeTwoThreeSpectrum4436.graph sourceMap2270=true := by decide +kernel
theorem fusedMap2270_checked : acceptsGraphIso
    (fused (graph core2270) (root 9) 0 4) DegreeTwoThreeSpectrum3994.graph fusedMap2270=true := by decide +kernel
theorem certified2270 : Certified (graph core2270) (root 9) 0 4 :=
  of_native_maps core2270 DegreeTwoThreeSpectrum4436.graph DegreeTwoThreeSpectrum3994.graph
    sourceMap2270 fusedMap2270 sourceMap2270_checked fusedMap2270_checked
    DegreeTwoThreeFiniteComparisons.comparison2270
#print axioms sourceMap2270_checked
#print axioms fusedMap2270_checked
#print axioms certified2270
def sourceMap2270swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2270swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2270swap_checked : acceptsGraphIso
    (source (graph core2270) (root 9) 4 0) DegreeTwoThreeSpectrum4436.graph sourceMap2270swap=true := by decide +kernel
theorem fusedMap2270swap_checked : acceptsGraphIso
    (fused (graph core2270) (root 9) 4 0) DegreeTwoThreeSpectrum3994.graph fusedMap2270swap=true := by decide +kernel
theorem certified2270swap : Certified (graph core2270) (root 9) 4 0 :=
  of_native_maps core2270 DegreeTwoThreeSpectrum4436.graph DegreeTwoThreeSpectrum3994.graph
    sourceMap2270swap fusedMap2270swap sourceMap2270swap_checked fusedMap2270swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2270
#print axioms sourceMap2270swap_checked
#print axioms fusedMap2270swap_checked
#print axioms certified2270swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
