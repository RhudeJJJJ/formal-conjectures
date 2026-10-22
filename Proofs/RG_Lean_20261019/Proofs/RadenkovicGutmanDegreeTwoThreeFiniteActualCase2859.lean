/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2859 : Family 10 := level10.get ⟨1216,by decide⟩
def sourceMap2859 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2859 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2859_checked : acceptsGraphIso
    (source (graph core2859) (root 10) 0 4) DegreeTwoThreeSpectrum6406.graph sourceMap2859=true := by decide +kernel
theorem fusedMap2859_checked : acceptsGraphIso
    (fused (graph core2859) (root 10) 0 4) DegreeTwoThreeSpectrum6407.graph fusedMap2859=true := by decide +kernel
theorem certified2859 : Certified (graph core2859) (root 10) 0 4 :=
  of_native_maps core2859 DegreeTwoThreeSpectrum6406.graph DegreeTwoThreeSpectrum6407.graph
    sourceMap2859 fusedMap2859 sourceMap2859_checked fusedMap2859_checked
    DegreeTwoThreeFiniteComparisons.comparison2859
#print axioms sourceMap2859_checked
#print axioms fusedMap2859_checked
#print axioms certified2859
def sourceMap2859swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2859swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2859swap_checked : acceptsGraphIso
    (source (graph core2859) (root 10) 4 0) DegreeTwoThreeSpectrum6406.graph sourceMap2859swap=true := by decide +kernel
theorem fusedMap2859swap_checked : acceptsGraphIso
    (fused (graph core2859) (root 10) 4 0) DegreeTwoThreeSpectrum6407.graph fusedMap2859swap=true := by decide +kernel
theorem certified2859swap : Certified (graph core2859) (root 10) 4 0 :=
  of_native_maps core2859 DegreeTwoThreeSpectrum6406.graph DegreeTwoThreeSpectrum6407.graph
    sourceMap2859swap fusedMap2859swap sourceMap2859swap_checked fusedMap2859swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2859
#print axioms sourceMap2859swap_checked
#print axioms fusedMap2859swap_checked
#print axioms certified2859swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
