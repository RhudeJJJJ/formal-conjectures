/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2700 : Family 10 := level10.get ⟨818,by decide⟩
def sourceMap2700 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2700 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2700_checked : acceptsGraphIso
    (source (graph core2700) (root 10) 0 4) DegreeTwoThreeSpectrum6780.graph sourceMap2700=true := by decide +kernel
theorem fusedMap2700_checked : acceptsGraphIso
    (fused (graph core2700) (root 10) 0 4) DegreeTwoThreeSpectrum5620.graph fusedMap2700=true := by decide +kernel
theorem certified2700 : Certified (graph core2700) (root 10) 0 4 :=
  of_native_maps core2700 DegreeTwoThreeSpectrum6780.graph DegreeTwoThreeSpectrum5620.graph
    sourceMap2700 fusedMap2700 sourceMap2700_checked fusedMap2700_checked
    DegreeTwoThreeFiniteComparisons.comparison2700
#print axioms sourceMap2700_checked
#print axioms fusedMap2700_checked
#print axioms certified2700
def sourceMap2700swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2700swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2700swap_checked : acceptsGraphIso
    (source (graph core2700) (root 10) 4 0) DegreeTwoThreeSpectrum6780.graph sourceMap2700swap=true := by decide +kernel
theorem fusedMap2700swap_checked : acceptsGraphIso
    (fused (graph core2700) (root 10) 4 0) DegreeTwoThreeSpectrum5620.graph fusedMap2700swap=true := by decide +kernel
theorem certified2700swap : Certified (graph core2700) (root 10) 4 0 :=
  of_native_maps core2700 DegreeTwoThreeSpectrum6780.graph DegreeTwoThreeSpectrum5620.graph
    sourceMap2700swap fusedMap2700swap sourceMap2700swap_checked fusedMap2700swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2700
#print axioms sourceMap2700swap_checked
#print axioms fusedMap2700swap_checked
#print axioms certified2700swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
