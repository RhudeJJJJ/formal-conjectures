/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2276 : Family 9 := level9.get ⟨230,by decide⟩
def sourceMap2276 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2276 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2276_checked : acceptsGraphIso
    (source (graph core2276) (root 9) 0 4) DegreeTwoThreeSpectrum4500.graph sourceMap2276=true := by decide +kernel
theorem fusedMap2276_checked : acceptsGraphIso
    (fused (graph core2276) (root 9) 0 4) DegreeTwoThreeSpectrum4022.graph fusedMap2276=true := by decide +kernel
theorem certified2276 : Certified (graph core2276) (root 9) 0 4 :=
  of_native_maps core2276 DegreeTwoThreeSpectrum4500.graph DegreeTwoThreeSpectrum4022.graph
    sourceMap2276 fusedMap2276 sourceMap2276_checked fusedMap2276_checked
    DegreeTwoThreeFiniteComparisons.comparison2276
#print axioms sourceMap2276_checked
#print axioms fusedMap2276_checked
#print axioms certified2276
def sourceMap2276swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2276swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2276swap_checked : acceptsGraphIso
    (source (graph core2276) (root 9) 4 0) DegreeTwoThreeSpectrum4500.graph sourceMap2276swap=true := by decide +kernel
theorem fusedMap2276swap_checked : acceptsGraphIso
    (fused (graph core2276) (root 9) 4 0) DegreeTwoThreeSpectrum4022.graph fusedMap2276swap=true := by decide +kernel
theorem certified2276swap : Certified (graph core2276) (root 9) 4 0 :=
  of_native_maps core2276 DegreeTwoThreeSpectrum4500.graph DegreeTwoThreeSpectrum4022.graph
    sourceMap2276swap fusedMap2276swap sourceMap2276swap_checked fusedMap2276swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2276
#print axioms sourceMap2276swap_checked
#print axioms fusedMap2276swap_checked
#print axioms certified2276swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
