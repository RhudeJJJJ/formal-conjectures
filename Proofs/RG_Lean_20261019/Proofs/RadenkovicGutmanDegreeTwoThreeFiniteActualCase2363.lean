/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2363 : Family 9 := level9.get ⟨455,by decide⟩
def sourceMap2363 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2363 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2363_checked : acceptsGraphIso
    (source (graph core2363) (root 9) 0 4) DegreeTwoThreeSpectrum4474.graph sourceMap2363=true := by decide +kernel
theorem fusedMap2363_checked : acceptsGraphIso
    (fused (graph core2363) (root 9) 0 4) DegreeTwoThreeSpectrum4475.graph fusedMap2363=true := by decide +kernel
theorem certified2363 : Certified (graph core2363) (root 9) 0 4 :=
  of_native_maps core2363 DegreeTwoThreeSpectrum4474.graph DegreeTwoThreeSpectrum4475.graph
    sourceMap2363 fusedMap2363 sourceMap2363_checked fusedMap2363_checked
    DegreeTwoThreeFiniteComparisons.comparison2363
#print axioms sourceMap2363_checked
#print axioms fusedMap2363_checked
#print axioms certified2363
def sourceMap2363swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2363swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2363swap_checked : acceptsGraphIso
    (source (graph core2363) (root 9) 4 0) DegreeTwoThreeSpectrum4474.graph sourceMap2363swap=true := by decide +kernel
theorem fusedMap2363swap_checked : acceptsGraphIso
    (fused (graph core2363) (root 9) 4 0) DegreeTwoThreeSpectrum4475.graph fusedMap2363swap=true := by decide +kernel
theorem certified2363swap : Certified (graph core2363) (root 9) 4 0 :=
  of_native_maps core2363 DegreeTwoThreeSpectrum4474.graph DegreeTwoThreeSpectrum4475.graph
    sourceMap2363swap fusedMap2363swap sourceMap2363swap_checked fusedMap2363swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2363
#print axioms sourceMap2363swap_checked
#print axioms fusedMap2363swap_checked
#print axioms certified2363swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
