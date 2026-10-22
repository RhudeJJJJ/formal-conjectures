/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2279 : Family 9 := level9.get ⟨237,by decide⟩
def sourceMap2279 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2279 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2279_checked : acceptsGraphIso
    (source (graph core2279) (root 9) 0 4) DegreeTwoThreeSpectrum4515.graph sourceMap2279=true := by decide +kernel
theorem fusedMap2279_checked : acceptsGraphIso
    (fused (graph core2279) (root 9) 0 4) DegreeTwoThreeSpectrum4031.graph fusedMap2279=true := by decide +kernel
theorem certified2279 : Certified (graph core2279) (root 9) 0 4 :=
  of_native_maps core2279 DegreeTwoThreeSpectrum4515.graph DegreeTwoThreeSpectrum4031.graph
    sourceMap2279 fusedMap2279 sourceMap2279_checked fusedMap2279_checked
    DegreeTwoThreeFiniteComparisons.comparison2279
#print axioms sourceMap2279_checked
#print axioms fusedMap2279_checked
#print axioms certified2279
def sourceMap2279swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2279swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2279swap_checked : acceptsGraphIso
    (source (graph core2279) (root 9) 4 0) DegreeTwoThreeSpectrum4515.graph sourceMap2279swap=true := by decide +kernel
theorem fusedMap2279swap_checked : acceptsGraphIso
    (fused (graph core2279) (root 9) 4 0) DegreeTwoThreeSpectrum4031.graph fusedMap2279swap=true := by decide +kernel
theorem certified2279swap : Certified (graph core2279) (root 9) 4 0 :=
  of_native_maps core2279 DegreeTwoThreeSpectrum4515.graph DegreeTwoThreeSpectrum4031.graph
    sourceMap2279swap fusedMap2279swap sourceMap2279swap_checked fusedMap2279swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2279
#print axioms sourceMap2279swap_checked
#print axioms fusedMap2279swap_checked
#print axioms certified2279swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
