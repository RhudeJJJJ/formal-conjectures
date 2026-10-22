/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2033 : Family 10 := level10.get ⟨1717,by decide⟩
def sourceMap2033 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2033 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2033_checked : acceptsGraphIso
    (source (graph core2033) (root 10) 0 2) DegreeTwoThreeSpectrum3827.graph sourceMap2033=true := by decide +kernel
theorem fusedMap2033_checked : acceptsGraphIso
    (fused (graph core2033) (root 10) 0 2) DegreeTwoThreeSpectrum3401.graph fusedMap2033=true := by decide +kernel
theorem certified2033 : Certified (graph core2033) (root 10) 0 2 :=
  of_native_maps core2033 DegreeTwoThreeSpectrum3827.graph DegreeTwoThreeSpectrum3401.graph
    sourceMap2033 fusedMap2033 sourceMap2033_checked fusedMap2033_checked
    DegreeTwoThreeFiniteComparisons.comparison2033
#print axioms sourceMap2033_checked
#print axioms fusedMap2033_checked
#print axioms certified2033
def sourceMap2033swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2033swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2033swap_checked : acceptsGraphIso
    (source (graph core2033) (root 10) 2 0) DegreeTwoThreeSpectrum3827.graph sourceMap2033swap=true := by decide +kernel
theorem fusedMap2033swap_checked : acceptsGraphIso
    (fused (graph core2033) (root 10) 2 0) DegreeTwoThreeSpectrum3401.graph fusedMap2033swap=true := by decide +kernel
theorem certified2033swap : Certified (graph core2033) (root 10) 2 0 :=
  of_native_maps core2033 DegreeTwoThreeSpectrum3827.graph DegreeTwoThreeSpectrum3401.graph
    sourceMap2033swap fusedMap2033swap sourceMap2033swap_checked fusedMap2033swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2033
#print axioms sourceMap2033swap_checked
#print axioms fusedMap2033swap_checked
#print axioms certified2033swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
