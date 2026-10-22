/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2331 : Family 9 := level9.get ⟨379,by decide⟩
def sourceMap2331 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2331 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2331_checked : acceptsGraphIso
    (source (graph core2331) (root 9) 0 4) DegreeTwoThreeSpectrum4314.graph sourceMap2331=true := by decide +kernel
theorem fusedMap2331_checked : acceptsGraphIso
    (fused (graph core2331) (root 9) 0 4) DegreeTwoThreeSpectrum4315.graph fusedMap2331=true := by decide +kernel
theorem certified2331 : Certified (graph core2331) (root 9) 0 4 :=
  of_native_maps core2331 DegreeTwoThreeSpectrum4314.graph DegreeTwoThreeSpectrum4315.graph
    sourceMap2331 fusedMap2331 sourceMap2331_checked fusedMap2331_checked
    DegreeTwoThreeFiniteComparisons.comparison2331
#print axioms sourceMap2331_checked
#print axioms fusedMap2331_checked
#print axioms certified2331
def sourceMap2331swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2331swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2331swap_checked : acceptsGraphIso
    (source (graph core2331) (root 9) 4 0) DegreeTwoThreeSpectrum4314.graph sourceMap2331swap=true := by decide +kernel
theorem fusedMap2331swap_checked : acceptsGraphIso
    (fused (graph core2331) (root 9) 4 0) DegreeTwoThreeSpectrum4315.graph fusedMap2331swap=true := by decide +kernel
theorem certified2331swap : Certified (graph core2331) (root 9) 4 0 :=
  of_native_maps core2331 DegreeTwoThreeSpectrum4314.graph DegreeTwoThreeSpectrum4315.graph
    sourceMap2331swap fusedMap2331swap sourceMap2331swap_checked fusedMap2331swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2331
#print axioms sourceMap2331swap_checked
#print axioms fusedMap2331swap_checked
#print axioms certified2331swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
