/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2391 : Family 9 := level9.get ⟨518,by decide⟩
def sourceMap2391 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2391 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2391_checked : acceptsGraphIso
    (source (graph core2391) (root 9) 0 4) DegreeTwoThreeSpectrum4609.graph sourceMap2391=true := by decide +kernel
theorem fusedMap2391_checked : acceptsGraphIso
    (fused (graph core2391) (root 9) 0 4) DegreeTwoThreeSpectrum4610.graph fusedMap2391=true := by decide +kernel
theorem certified2391 : Certified (graph core2391) (root 9) 0 4 :=
  of_native_maps core2391 DegreeTwoThreeSpectrum4609.graph DegreeTwoThreeSpectrum4610.graph
    sourceMap2391 fusedMap2391 sourceMap2391_checked fusedMap2391_checked
    DegreeTwoThreeFiniteComparisons.comparison2391
#print axioms sourceMap2391_checked
#print axioms fusedMap2391_checked
#print axioms certified2391
def sourceMap2391swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2391swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2391swap_checked : acceptsGraphIso
    (source (graph core2391) (root 9) 4 0) DegreeTwoThreeSpectrum4609.graph sourceMap2391swap=true := by decide +kernel
theorem fusedMap2391swap_checked : acceptsGraphIso
    (fused (graph core2391) (root 9) 4 0) DegreeTwoThreeSpectrum4610.graph fusedMap2391swap=true := by decide +kernel
theorem certified2391swap : Certified (graph core2391) (root 9) 4 0 :=
  of_native_maps core2391 DegreeTwoThreeSpectrum4609.graph DegreeTwoThreeSpectrum4610.graph
    sourceMap2391swap fusedMap2391swap sourceMap2391swap_checked fusedMap2391swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2391
#print axioms sourceMap2391swap_checked
#print axioms fusedMap2391swap_checked
#print axioms certified2391swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
