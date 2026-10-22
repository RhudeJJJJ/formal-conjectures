/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2313 : Family 9 := level9.get ⟨328,by decide⟩
def sourceMap2313 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2313 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2313_checked : acceptsGraphIso
    (source (graph core2313) (root 9) 0 4) DegreeTwoThreeSpectrum4200.graph sourceMap2313=true := by decide +kernel
theorem fusedMap2313_checked : acceptsGraphIso
    (fused (graph core2313) (root 9) 0 4) DegreeTwoThreeSpectrum4201.graph fusedMap2313=true := by decide +kernel
theorem certified2313 : Certified (graph core2313) (root 9) 0 4 :=
  of_native_maps core2313 DegreeTwoThreeSpectrum4200.graph DegreeTwoThreeSpectrum4201.graph
    sourceMap2313 fusedMap2313 sourceMap2313_checked fusedMap2313_checked
    DegreeTwoThreeFiniteComparisons.comparison2313
#print axioms sourceMap2313_checked
#print axioms fusedMap2313_checked
#print axioms certified2313
def sourceMap2313swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2313swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2313swap_checked : acceptsGraphIso
    (source (graph core2313) (root 9) 4 0) DegreeTwoThreeSpectrum4200.graph sourceMap2313swap=true := by decide +kernel
theorem fusedMap2313swap_checked : acceptsGraphIso
    (fused (graph core2313) (root 9) 4 0) DegreeTwoThreeSpectrum4201.graph fusedMap2313swap=true := by decide +kernel
theorem certified2313swap : Certified (graph core2313) (root 9) 4 0 :=
  of_native_maps core2313 DegreeTwoThreeSpectrum4200.graph DegreeTwoThreeSpectrum4201.graph
    sourceMap2313swap fusedMap2313swap sourceMap2313swap_checked fusedMap2313swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2313
#print axioms sourceMap2313swap_checked
#print axioms fusedMap2313swap_checked
#print axioms certified2313swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
