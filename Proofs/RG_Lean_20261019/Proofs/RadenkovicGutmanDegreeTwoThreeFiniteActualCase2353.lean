/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2353 : Family 9 := level9.get ⟨432,by decide⟩
def sourceMap2353 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2353 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2353_checked : acceptsGraphIso
    (source (graph core2353) (root 9) 0 4) DegreeTwoThreeSpectrum4426.graph sourceMap2353=true := by decide +kernel
theorem fusedMap2353_checked : acceptsGraphIso
    (fused (graph core2353) (root 9) 0 4) DegreeTwoThreeSpectrum4427.graph fusedMap2353=true := by decide +kernel
theorem certified2353 : Certified (graph core2353) (root 9) 0 4 :=
  of_native_maps core2353 DegreeTwoThreeSpectrum4426.graph DegreeTwoThreeSpectrum4427.graph
    sourceMap2353 fusedMap2353 sourceMap2353_checked fusedMap2353_checked
    DegreeTwoThreeFiniteComparisons.comparison2353
#print axioms sourceMap2353_checked
#print axioms fusedMap2353_checked
#print axioms certified2353
def sourceMap2353swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2353swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2353swap_checked : acceptsGraphIso
    (source (graph core2353) (root 9) 4 0) DegreeTwoThreeSpectrum4426.graph sourceMap2353swap=true := by decide +kernel
theorem fusedMap2353swap_checked : acceptsGraphIso
    (fused (graph core2353) (root 9) 4 0) DegreeTwoThreeSpectrum4427.graph fusedMap2353swap=true := by decide +kernel
theorem certified2353swap : Certified (graph core2353) (root 9) 4 0 :=
  of_native_maps core2353 DegreeTwoThreeSpectrum4426.graph DegreeTwoThreeSpectrum4427.graph
    sourceMap2353swap fusedMap2353swap sourceMap2353swap_checked fusedMap2353swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2353
#print axioms sourceMap2353swap_checked
#print axioms fusedMap2353swap_checked
#print axioms certified2353swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
