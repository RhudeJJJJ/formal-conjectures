/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2819 : Family 10 := level10.get ⟨1123,by decide⟩
def sourceMap2819 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2819 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2819_checked : acceptsGraphIso
    (source (graph core2819) (root 10) 0 4) DegreeTwoThreeSpectrum6231.graph sourceMap2819=true := by decide +kernel
theorem fusedMap2819_checked : acceptsGraphIso
    (fused (graph core2819) (root 10) 0 4) DegreeTwoThreeSpectrum6232.graph fusedMap2819=true := by decide +kernel
theorem certified2819 : Certified (graph core2819) (root 10) 0 4 :=
  of_native_maps core2819 DegreeTwoThreeSpectrum6231.graph DegreeTwoThreeSpectrum6232.graph
    sourceMap2819 fusedMap2819 sourceMap2819_checked fusedMap2819_checked
    DegreeTwoThreeFiniteComparisons.comparison2819
#print axioms sourceMap2819_checked
#print axioms fusedMap2819_checked
#print axioms certified2819
def sourceMap2819swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2819swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2819swap_checked : acceptsGraphIso
    (source (graph core2819) (root 10) 4 0) DegreeTwoThreeSpectrum6231.graph sourceMap2819swap=true := by decide +kernel
theorem fusedMap2819swap_checked : acceptsGraphIso
    (fused (graph core2819) (root 10) 4 0) DegreeTwoThreeSpectrum6232.graph fusedMap2819swap=true := by decide +kernel
theorem certified2819swap : Certified (graph core2819) (root 10) 4 0 :=
  of_native_maps core2819 DegreeTwoThreeSpectrum6231.graph DegreeTwoThreeSpectrum6232.graph
    sourceMap2819swap fusedMap2819swap sourceMap2819swap_checked fusedMap2819swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2819
#print axioms sourceMap2819swap_checked
#print axioms fusedMap2819swap_checked
#print axioms certified2819swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
