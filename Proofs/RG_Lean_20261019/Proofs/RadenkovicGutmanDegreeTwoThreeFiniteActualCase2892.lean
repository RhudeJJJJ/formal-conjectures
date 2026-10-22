/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2892 : Family 10 := level10.get ⟨1302,by decide⟩
def sourceMap2892 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2892 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2892_checked : acceptsGraphIso
    (source (graph core2892) (root 10) 0 4) DegreeTwoThreeSpectrum6591.graph sourceMap2892=true := by decide +kernel
theorem fusedMap2892_checked : acceptsGraphIso
    (fused (graph core2892) (root 10) 0 4) DegreeTwoThreeSpectrum6592.graph fusedMap2892=true := by decide +kernel
theorem certified2892 : Certified (graph core2892) (root 10) 0 4 :=
  of_native_maps core2892 DegreeTwoThreeSpectrum6591.graph DegreeTwoThreeSpectrum6592.graph
    sourceMap2892 fusedMap2892 sourceMap2892_checked fusedMap2892_checked
    DegreeTwoThreeFiniteComparisons.comparison2892
#print axioms sourceMap2892_checked
#print axioms fusedMap2892_checked
#print axioms certified2892
def sourceMap2892swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2892swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2892swap_checked : acceptsGraphIso
    (source (graph core2892) (root 10) 4 0) DegreeTwoThreeSpectrum6591.graph sourceMap2892swap=true := by decide +kernel
theorem fusedMap2892swap_checked : acceptsGraphIso
    (fused (graph core2892) (root 10) 4 0) DegreeTwoThreeSpectrum6592.graph fusedMap2892swap=true := by decide +kernel
theorem certified2892swap : Certified (graph core2892) (root 10) 4 0 :=
  of_native_maps core2892 DegreeTwoThreeSpectrum6591.graph DegreeTwoThreeSpectrum6592.graph
    sourceMap2892swap fusedMap2892swap sourceMap2892swap_checked fusedMap2892swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2892
#print axioms sourceMap2892swap_checked
#print axioms fusedMap2892swap_checked
#print axioms certified2892swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
