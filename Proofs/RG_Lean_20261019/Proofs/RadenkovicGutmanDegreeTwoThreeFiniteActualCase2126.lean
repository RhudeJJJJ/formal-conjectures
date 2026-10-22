/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2126 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap2126 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2126 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2126_checked : acceptsGraphIso
    (source (graph core2126) (root 8) 0 4) DegreeTwoThreeSpectrum2501.graph sourceMap2126=true := by decide +kernel
theorem fusedMap2126_checked : acceptsGraphIso
    (fused (graph core2126) (root 8) 0 4) DegreeTwoThreeSpectrum2318.graph fusedMap2126=true := by decide +kernel
theorem certified2126 : Certified (graph core2126) (root 8) 0 4 :=
  of_native_maps core2126 DegreeTwoThreeSpectrum2501.graph DegreeTwoThreeSpectrum2318.graph
    sourceMap2126 fusedMap2126 sourceMap2126_checked fusedMap2126_checked
    DegreeTwoThreeFiniteComparisons.comparison2126
#print axioms sourceMap2126_checked
#print axioms fusedMap2126_checked
#print axioms certified2126
def sourceMap2126swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2126swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2126swap_checked : acceptsGraphIso
    (source (graph core2126) (root 8) 4 0) DegreeTwoThreeSpectrum2501.graph sourceMap2126swap=true := by decide +kernel
theorem fusedMap2126swap_checked : acceptsGraphIso
    (fused (graph core2126) (root 8) 4 0) DegreeTwoThreeSpectrum2318.graph fusedMap2126swap=true := by decide +kernel
theorem certified2126swap : Certified (graph core2126) (root 8) 4 0 :=
  of_native_maps core2126 DegreeTwoThreeSpectrum2501.graph DegreeTwoThreeSpectrum2318.graph
    sourceMap2126swap fusedMap2126swap sourceMap2126swap_checked fusedMap2126swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2126
#print axioms sourceMap2126swap_checked
#print axioms fusedMap2126swap_checked
#print axioms certified2126swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
