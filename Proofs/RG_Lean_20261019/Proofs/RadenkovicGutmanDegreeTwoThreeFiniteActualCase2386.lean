/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2386 : Family 9 := level9.get ⟨510,by decide⟩
def sourceMap2386 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2386 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2386_checked : acceptsGraphIso
    (source (graph core2386) (root 9) 0 4) DegreeTwoThreeSpectrum4593.graph sourceMap2386=true := by decide +kernel
theorem fusedMap2386_checked : acceptsGraphIso
    (fused (graph core2386) (root 9) 0 4) DegreeTwoThreeSpectrum4594.graph fusedMap2386=true := by decide +kernel
theorem certified2386 : Certified (graph core2386) (root 9) 0 4 :=
  of_native_maps core2386 DegreeTwoThreeSpectrum4593.graph DegreeTwoThreeSpectrum4594.graph
    sourceMap2386 fusedMap2386 sourceMap2386_checked fusedMap2386_checked
    DegreeTwoThreeFiniteComparisons.comparison2386
#print axioms sourceMap2386_checked
#print axioms fusedMap2386_checked
#print axioms certified2386
def sourceMap2386swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2386swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2386swap_checked : acceptsGraphIso
    (source (graph core2386) (root 9) 4 0) DegreeTwoThreeSpectrum4593.graph sourceMap2386swap=true := by decide +kernel
theorem fusedMap2386swap_checked : acceptsGraphIso
    (fused (graph core2386) (root 9) 4 0) DegreeTwoThreeSpectrum4594.graph fusedMap2386swap=true := by decide +kernel
theorem certified2386swap : Certified (graph core2386) (root 9) 4 0 :=
  of_native_maps core2386 DegreeTwoThreeSpectrum4593.graph DegreeTwoThreeSpectrum4594.graph
    sourceMap2386swap fusedMap2386swap sourceMap2386swap_checked fusedMap2386swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2386
#print axioms sourceMap2386swap_checked
#print axioms fusedMap2386swap_checked
#print axioms certified2386swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
