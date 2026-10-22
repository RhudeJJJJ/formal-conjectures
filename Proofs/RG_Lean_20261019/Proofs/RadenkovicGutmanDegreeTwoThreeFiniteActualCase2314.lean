/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2314 : Family 9 := level9.get ⟨333,by decide⟩
def sourceMap2314 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2314 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2314_checked : acceptsGraphIso
    (source (graph core2314) (root 9) 0 4) DegreeTwoThreeSpectrum4214.graph sourceMap2314=true := by decide +kernel
theorem fusedMap2314_checked : acceptsGraphIso
    (fused (graph core2314) (root 9) 0 4) DegreeTwoThreeSpectrum4215.graph fusedMap2314=true := by decide +kernel
theorem certified2314 : Certified (graph core2314) (root 9) 0 4 :=
  of_native_maps core2314 DegreeTwoThreeSpectrum4214.graph DegreeTwoThreeSpectrum4215.graph
    sourceMap2314 fusedMap2314 sourceMap2314_checked fusedMap2314_checked
    DegreeTwoThreeFiniteComparisons.comparison2314
#print axioms sourceMap2314_checked
#print axioms fusedMap2314_checked
#print axioms certified2314
def sourceMap2314swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2314swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2314swap_checked : acceptsGraphIso
    (source (graph core2314) (root 9) 4 0) DegreeTwoThreeSpectrum4214.graph sourceMap2314swap=true := by decide +kernel
theorem fusedMap2314swap_checked : acceptsGraphIso
    (fused (graph core2314) (root 9) 4 0) DegreeTwoThreeSpectrum4215.graph fusedMap2314swap=true := by decide +kernel
theorem certified2314swap : Certified (graph core2314) (root 9) 4 0 :=
  of_native_maps core2314 DegreeTwoThreeSpectrum4214.graph DegreeTwoThreeSpectrum4215.graph
    sourceMap2314swap fusedMap2314swap sourceMap2314swap_checked fusedMap2314swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2314
#print axioms sourceMap2314swap_checked
#print axioms fusedMap2314swap_checked
#print axioms certified2314swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
