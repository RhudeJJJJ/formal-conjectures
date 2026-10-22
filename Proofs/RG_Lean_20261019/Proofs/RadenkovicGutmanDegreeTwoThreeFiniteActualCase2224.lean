/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2224 : Family 9 := level9.get ⟨54,by decide⟩
def sourceMap2224 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2224 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2224_checked : acceptsGraphIso
    (source (graph core2224) (root 9) 0 4) DegreeTwoThreeSpectrum3939.graph sourceMap2224=true := by decide +kernel
theorem fusedMap2224_checked : acceptsGraphIso
    (fused (graph core2224) (root 9) 0 4) DegreeTwoThreeSpectrum3940.graph fusedMap2224=true := by decide +kernel
theorem certified2224 : Certified (graph core2224) (root 9) 0 4 :=
  of_native_maps core2224 DegreeTwoThreeSpectrum3939.graph DegreeTwoThreeSpectrum3940.graph
    sourceMap2224 fusedMap2224 sourceMap2224_checked fusedMap2224_checked
    DegreeTwoThreeFiniteComparisons.comparison2224
#print axioms sourceMap2224_checked
#print axioms fusedMap2224_checked
#print axioms certified2224
def sourceMap2224swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2224swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2224swap_checked : acceptsGraphIso
    (source (graph core2224) (root 9) 4 0) DegreeTwoThreeSpectrum3939.graph sourceMap2224swap=true := by decide +kernel
theorem fusedMap2224swap_checked : acceptsGraphIso
    (fused (graph core2224) (root 9) 4 0) DegreeTwoThreeSpectrum3940.graph fusedMap2224swap=true := by decide +kernel
theorem certified2224swap : Certified (graph core2224) (root 9) 4 0 :=
  of_native_maps core2224 DegreeTwoThreeSpectrum3939.graph DegreeTwoThreeSpectrum3940.graph
    sourceMap2224swap fusedMap2224swap sourceMap2224swap_checked fusedMap2224swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2224
#print axioms sourceMap2224swap_checked
#print axioms fusedMap2224swap_checked
#print axioms certified2224swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
