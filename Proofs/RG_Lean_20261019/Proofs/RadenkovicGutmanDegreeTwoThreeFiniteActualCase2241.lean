/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2241 : Family 9 := level9.get ⟨119,by decide⟩
def sourceMap2241 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2241 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2241_checked : acceptsGraphIso
    (source (graph core2241) (root 9) 0 4) DegreeTwoThreeSpectrum4137.graph sourceMap2241=true := by decide +kernel
theorem fusedMap2241_checked : acceptsGraphIso
    (fused (graph core2241) (root 9) 0 4) DegreeTwoThreeSpectrum4138.graph fusedMap2241=true := by decide +kernel
theorem certified2241 : Certified (graph core2241) (root 9) 0 4 :=
  of_native_maps core2241 DegreeTwoThreeSpectrum4137.graph DegreeTwoThreeSpectrum4138.graph
    sourceMap2241 fusedMap2241 sourceMap2241_checked fusedMap2241_checked
    DegreeTwoThreeFiniteComparisons.comparison2241
#print axioms sourceMap2241_checked
#print axioms fusedMap2241_checked
#print axioms certified2241
def sourceMap2241swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2241swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2241swap_checked : acceptsGraphIso
    (source (graph core2241) (root 9) 4 0) DegreeTwoThreeSpectrum4137.graph sourceMap2241swap=true := by decide +kernel
theorem fusedMap2241swap_checked : acceptsGraphIso
    (fused (graph core2241) (root 9) 4 0) DegreeTwoThreeSpectrum4138.graph fusedMap2241swap=true := by decide +kernel
theorem certified2241swap : Certified (graph core2241) (root 9) 4 0 :=
  of_native_maps core2241 DegreeTwoThreeSpectrum4137.graph DegreeTwoThreeSpectrum4138.graph
    sourceMap2241swap fusedMap2241swap sourceMap2241swap_checked fusedMap2241swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2241
#print axioms sourceMap2241swap_checked
#print axioms fusedMap2241swap_checked
#print axioms certified2241swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
