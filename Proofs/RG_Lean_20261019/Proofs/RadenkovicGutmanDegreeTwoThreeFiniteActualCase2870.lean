/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2870 : Family 10 := level10.get ⟨1247,by decide⟩
def sourceMap2870 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2870 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2870_checked : acceptsGraphIso
    (source (graph core2870) (root 10) 0 4) DegreeTwoThreeSpectrum6482.graph sourceMap2870=true := by decide +kernel
theorem fusedMap2870_checked : acceptsGraphIso
    (fused (graph core2870) (root 10) 0 4) DegreeTwoThreeSpectrum6483.graph fusedMap2870=true := by decide +kernel
theorem certified2870 : Certified (graph core2870) (root 10) 0 4 :=
  of_native_maps core2870 DegreeTwoThreeSpectrum6482.graph DegreeTwoThreeSpectrum6483.graph
    sourceMap2870 fusedMap2870 sourceMap2870_checked fusedMap2870_checked
    DegreeTwoThreeFiniteComparisons.comparison2870
#print axioms sourceMap2870_checked
#print axioms fusedMap2870_checked
#print axioms certified2870
def sourceMap2870swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2870swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2870swap_checked : acceptsGraphIso
    (source (graph core2870) (root 10) 4 0) DegreeTwoThreeSpectrum6482.graph sourceMap2870swap=true := by decide +kernel
theorem fusedMap2870swap_checked : acceptsGraphIso
    (fused (graph core2870) (root 10) 4 0) DegreeTwoThreeSpectrum6483.graph fusedMap2870swap=true := by decide +kernel
theorem certified2870swap : Certified (graph core2870) (root 10) 4 0 :=
  of_native_maps core2870 DegreeTwoThreeSpectrum6482.graph DegreeTwoThreeSpectrum6483.graph
    sourceMap2870swap fusedMap2870swap sourceMap2870swap_checked fusedMap2870swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2870
#print axioms sourceMap2870swap_checked
#print axioms fusedMap2870swap_checked
#print axioms certified2870swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
