/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2393 : Family 9 := level9.get ⟨521,by decide⟩
def sourceMap2393 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2393 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2393_checked : acceptsGraphIso
    (source (graph core2393) (root 9) 0 4) DegreeTwoThreeSpectrum4615.graph sourceMap2393=true := by decide +kernel
theorem fusedMap2393_checked : acceptsGraphIso
    (fused (graph core2393) (root 9) 0 4) DegreeTwoThreeSpectrum4616.graph fusedMap2393=true := by decide +kernel
theorem certified2393 : Certified (graph core2393) (root 9) 0 4 :=
  of_native_maps core2393 DegreeTwoThreeSpectrum4615.graph DegreeTwoThreeSpectrum4616.graph
    sourceMap2393 fusedMap2393 sourceMap2393_checked fusedMap2393_checked
    DegreeTwoThreeFiniteComparisons.comparison2393
#print axioms sourceMap2393_checked
#print axioms fusedMap2393_checked
#print axioms certified2393
def sourceMap2393swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2393swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2393swap_checked : acceptsGraphIso
    (source (graph core2393) (root 9) 4 0) DegreeTwoThreeSpectrum4615.graph sourceMap2393swap=true := by decide +kernel
theorem fusedMap2393swap_checked : acceptsGraphIso
    (fused (graph core2393) (root 9) 4 0) DegreeTwoThreeSpectrum4616.graph fusedMap2393swap=true := by decide +kernel
theorem certified2393swap : Certified (graph core2393) (root 9) 4 0 :=
  of_native_maps core2393 DegreeTwoThreeSpectrum4615.graph DegreeTwoThreeSpectrum4616.graph
    sourceMap2393swap fusedMap2393swap sourceMap2393swap_checked fusedMap2393swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2393
#print axioms sourceMap2393swap_checked
#print axioms fusedMap2393swap_checked
#print axioms certified2393swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
