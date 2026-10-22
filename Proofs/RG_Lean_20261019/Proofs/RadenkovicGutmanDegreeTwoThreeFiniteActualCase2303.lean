/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2303 : Family 9 := level9.get ⟨302,by decide⟩
def sourceMap2303 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2303 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2303_checked : acceptsGraphIso
    (source (graph core2303) (root 9) 0 4) DegreeTwoThreeSpectrum4654.graph sourceMap2303=true := by decide +kernel
theorem fusedMap2303_checked : acceptsGraphIso
    (fused (graph core2303) (root 9) 0 4) DegreeTwoThreeSpectrum4134.graph fusedMap2303=true := by decide +kernel
theorem certified2303 : Certified (graph core2303) (root 9) 0 4 :=
  of_native_maps core2303 DegreeTwoThreeSpectrum4654.graph DegreeTwoThreeSpectrum4134.graph
    sourceMap2303 fusedMap2303 sourceMap2303_checked fusedMap2303_checked
    DegreeTwoThreeFiniteComparisons.comparison2303
#print axioms sourceMap2303_checked
#print axioms fusedMap2303_checked
#print axioms certified2303
def sourceMap2303swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2303swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2303swap_checked : acceptsGraphIso
    (source (graph core2303) (root 9) 4 0) DegreeTwoThreeSpectrum4654.graph sourceMap2303swap=true := by decide +kernel
theorem fusedMap2303swap_checked : acceptsGraphIso
    (fused (graph core2303) (root 9) 4 0) DegreeTwoThreeSpectrum4134.graph fusedMap2303swap=true := by decide +kernel
theorem certified2303swap : Certified (graph core2303) (root 9) 4 0 :=
  of_native_maps core2303 DegreeTwoThreeSpectrum4654.graph DegreeTwoThreeSpectrum4134.graph
    sourceMap2303swap fusedMap2303swap sourceMap2303swap_checked fusedMap2303swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2303
#print axioms sourceMap2303swap_checked
#print axioms fusedMap2303swap_checked
#print axioms certified2303swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
