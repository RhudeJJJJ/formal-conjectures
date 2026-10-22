/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2375 : Family 9 := level9.get ⟨481,by decide⟩
def sourceMap2375 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2375 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2375_checked : acceptsGraphIso
    (source (graph core2375) (root 9) 0 4) DegreeTwoThreeSpectrum4524.graph sourceMap2375=true := by decide +kernel
theorem fusedMap2375_checked : acceptsGraphIso
    (fused (graph core2375) (root 9) 0 4) DegreeTwoThreeSpectrum4525.graph fusedMap2375=true := by decide +kernel
theorem certified2375 : Certified (graph core2375) (root 9) 0 4 :=
  of_native_maps core2375 DegreeTwoThreeSpectrum4524.graph DegreeTwoThreeSpectrum4525.graph
    sourceMap2375 fusedMap2375 sourceMap2375_checked fusedMap2375_checked
    DegreeTwoThreeFiniteComparisons.comparison2375
#print axioms sourceMap2375_checked
#print axioms fusedMap2375_checked
#print axioms certified2375
def sourceMap2375swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2375swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2375swap_checked : acceptsGraphIso
    (source (graph core2375) (root 9) 4 0) DegreeTwoThreeSpectrum4524.graph sourceMap2375swap=true := by decide +kernel
theorem fusedMap2375swap_checked : acceptsGraphIso
    (fused (graph core2375) (root 9) 4 0) DegreeTwoThreeSpectrum4525.graph fusedMap2375swap=true := by decide +kernel
theorem certified2375swap : Certified (graph core2375) (root 9) 4 0 :=
  of_native_maps core2375 DegreeTwoThreeSpectrum4524.graph DegreeTwoThreeSpectrum4525.graph
    sourceMap2375swap fusedMap2375swap sourceMap2375swap_checked fusedMap2375swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2375
#print axioms sourceMap2375swap_checked
#print axioms fusedMap2375swap_checked
#print axioms certified2375swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
