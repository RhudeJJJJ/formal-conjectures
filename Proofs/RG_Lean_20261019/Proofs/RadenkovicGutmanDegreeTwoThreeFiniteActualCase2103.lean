/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2103 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap2103 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2103 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2103_checked : acceptsGraphIso
    (source (graph core2103) (root 7) 0 4) DegreeTwoThreeSpectrum1973.graph sourceMap2103=true := by decide +kernel
theorem fusedMap2103_checked : acceptsGraphIso
    (fused (graph core2103) (root 7) 0 4) DegreeTwoThreeSpectrum1747.graph fusedMap2103=true := by decide +kernel
theorem certified2103 : Certified (graph core2103) (root 7) 0 4 :=
  of_native_maps core2103 DegreeTwoThreeSpectrum1973.graph DegreeTwoThreeSpectrum1747.graph
    sourceMap2103 fusedMap2103 sourceMap2103_checked fusedMap2103_checked
    DegreeTwoThreeFiniteComparisons.comparison2103
#print axioms sourceMap2103_checked
#print axioms fusedMap2103_checked
#print axioms certified2103
def sourceMap2103swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,9] (sourceLabel 7 4 0 v)
def fusedMap2103swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2103swap_checked : acceptsGraphIso
    (source (graph core2103) (root 7) 4 0) DegreeTwoThreeSpectrum1973.graph sourceMap2103swap=true := by decide +kernel
theorem fusedMap2103swap_checked : acceptsGraphIso
    (fused (graph core2103) (root 7) 4 0) DegreeTwoThreeSpectrum1747.graph fusedMap2103swap=true := by decide +kernel
theorem certified2103swap : Certified (graph core2103) (root 7) 4 0 :=
  of_native_maps core2103 DegreeTwoThreeSpectrum1973.graph DegreeTwoThreeSpectrum1747.graph
    sourceMap2103swap fusedMap2103swap sourceMap2103swap_checked fusedMap2103swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2103
#print axioms sourceMap2103swap_checked
#print axioms fusedMap2103swap_checked
#print axioms certified2103swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
