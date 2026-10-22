/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2146 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap2146 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2146 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2146_checked : acceptsGraphIso
    (source (graph core2146) (root 8) 0 4) DegreeTwoThreeSpectrum2467.graph sourceMap2146=true := by decide +kernel
theorem fusedMap2146_checked : acceptsGraphIso
    (fused (graph core2146) (root 8) 0 4) DegreeTwoThreeSpectrum2469.graph fusedMap2146=true := by decide +kernel
theorem certified2146 : Certified (graph core2146) (root 8) 0 4 :=
  of_native_maps core2146 DegreeTwoThreeSpectrum2467.graph DegreeTwoThreeSpectrum2469.graph
    sourceMap2146 fusedMap2146 sourceMap2146_checked fusedMap2146_checked
    DegreeTwoThreeFiniteComparisons.comparison2146
#print axioms sourceMap2146_checked
#print axioms fusedMap2146_checked
#print axioms certified2146
def sourceMap2146swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2146swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2146swap_checked : acceptsGraphIso
    (source (graph core2146) (root 8) 4 0) DegreeTwoThreeSpectrum2467.graph sourceMap2146swap=true := by decide +kernel
theorem fusedMap2146swap_checked : acceptsGraphIso
    (fused (graph core2146) (root 8) 4 0) DegreeTwoThreeSpectrum2469.graph fusedMap2146swap=true := by decide +kernel
theorem certified2146swap : Certified (graph core2146) (root 8) 4 0 :=
  of_native_maps core2146 DegreeTwoThreeSpectrum2467.graph DegreeTwoThreeSpectrum2469.graph
    sourceMap2146swap fusedMap2146swap sourceMap2146swap_checked fusedMap2146swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2146
#print axioms sourceMap2146swap_checked
#print axioms fusedMap2146swap_checked
#print axioms certified2146swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
