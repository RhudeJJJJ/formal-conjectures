/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2336 : Family 9 := level9.get ⟨392,by decide⟩
def sourceMap2336 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2336 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2336_checked : acceptsGraphIso
    (source (graph core2336) (root 9) 0 4) DegreeTwoThreeSpectrum4344.graph sourceMap2336=true := by decide +kernel
theorem fusedMap2336_checked : acceptsGraphIso
    (fused (graph core2336) (root 9) 0 4) DegreeTwoThreeSpectrum4345.graph fusedMap2336=true := by decide +kernel
theorem certified2336 : Certified (graph core2336) (root 9) 0 4 :=
  of_native_maps core2336 DegreeTwoThreeSpectrum4344.graph DegreeTwoThreeSpectrum4345.graph
    sourceMap2336 fusedMap2336 sourceMap2336_checked fusedMap2336_checked
    DegreeTwoThreeFiniteComparisons.comparison2336
#print axioms sourceMap2336_checked
#print axioms fusedMap2336_checked
#print axioms certified2336
def sourceMap2336swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2336swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2336swap_checked : acceptsGraphIso
    (source (graph core2336) (root 9) 4 0) DegreeTwoThreeSpectrum4344.graph sourceMap2336swap=true := by decide +kernel
theorem fusedMap2336swap_checked : acceptsGraphIso
    (fused (graph core2336) (root 9) 4 0) DegreeTwoThreeSpectrum4345.graph fusedMap2336swap=true := by decide +kernel
theorem certified2336swap : Certified (graph core2336) (root 9) 4 0 :=
  of_native_maps core2336 DegreeTwoThreeSpectrum4344.graph DegreeTwoThreeSpectrum4345.graph
    sourceMap2336swap fusedMap2336swap sourceMap2336swap_checked fusedMap2336swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2336
#print axioms sourceMap2336swap_checked
#print axioms fusedMap2336swap_checked
#print axioms certified2336swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
