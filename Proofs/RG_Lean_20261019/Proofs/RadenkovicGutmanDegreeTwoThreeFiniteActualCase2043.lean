/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2043 : Family 10 := level10.get ⟨1746,by decide⟩
def sourceMap2043 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap2043 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2043_checked : acceptsGraphIso
    (source (graph core2043) (root 10) 0 2) DegreeTwoThreeSpectrum3841.graph sourceMap2043=true := by decide +kernel
theorem fusedMap2043_checked : acceptsGraphIso
    (fused (graph core2043) (root 10) 0 2) DegreeTwoThreeSpectrum3473.graph fusedMap2043=true := by decide +kernel
theorem certified2043 : Certified (graph core2043) (root 10) 0 2 :=
  of_native_maps core2043 DegreeTwoThreeSpectrum3841.graph DegreeTwoThreeSpectrum3473.graph
    sourceMap2043 fusedMap2043 sourceMap2043_checked fusedMap2043_checked
    DegreeTwoThreeFiniteComparisons.comparison2043
#print axioms sourceMap2043_checked
#print axioms fusedMap2043_checked
#print axioms certified2043
def sourceMap2043swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap2043swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2043swap_checked : acceptsGraphIso
    (source (graph core2043) (root 10) 2 0) DegreeTwoThreeSpectrum3841.graph sourceMap2043swap=true := by decide +kernel
theorem fusedMap2043swap_checked : acceptsGraphIso
    (fused (graph core2043) (root 10) 2 0) DegreeTwoThreeSpectrum3473.graph fusedMap2043swap=true := by decide +kernel
theorem certified2043swap : Certified (graph core2043) (root 10) 2 0 :=
  of_native_maps core2043 DegreeTwoThreeSpectrum3841.graph DegreeTwoThreeSpectrum3473.graph
    sourceMap2043swap fusedMap2043swap sourceMap2043swap_checked fusedMap2043swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2043
#print axioms sourceMap2043swap_checked
#print axioms fusedMap2043swap_checked
#print axioms certified2043swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
