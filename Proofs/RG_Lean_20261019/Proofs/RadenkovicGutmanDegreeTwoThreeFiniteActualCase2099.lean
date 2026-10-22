/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2099 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap2099 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2099 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2099_checked : acceptsGraphIso
    (source (graph core2099) (root 7) 0 4) DegreeTwoThreeSpectrum1905.graph sourceMap2099=true := by decide +kernel
theorem fusedMap2099_checked : acceptsGraphIso
    (fused (graph core2099) (root 7) 0 4) DegreeTwoThreeSpectrum1907.graph fusedMap2099=true := by decide +kernel
theorem certified2099 : Certified (graph core2099) (root 7) 0 4 :=
  of_native_maps core2099 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1907.graph
    sourceMap2099 fusedMap2099 sourceMap2099_checked fusedMap2099_checked
    DegreeTwoThreeFiniteComparisons.comparison2099
#print axioms sourceMap2099_checked
#print axioms fusedMap2099_checked
#print axioms certified2099
def sourceMap2099swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2099swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2099swap_checked : acceptsGraphIso
    (source (graph core2099) (root 7) 4 0) DegreeTwoThreeSpectrum1905.graph sourceMap2099swap=true := by decide +kernel
theorem fusedMap2099swap_checked : acceptsGraphIso
    (fused (graph core2099) (root 7) 4 0) DegreeTwoThreeSpectrum1907.graph fusedMap2099swap=true := by decide +kernel
theorem certified2099swap : Certified (graph core2099) (root 7) 4 0 :=
  of_native_maps core2099 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1907.graph
    sourceMap2099swap fusedMap2099swap sourceMap2099swap_checked fusedMap2099swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2099
#print axioms sourceMap2099swap_checked
#print axioms fusedMap2099swap_checked
#print axioms certified2099swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
