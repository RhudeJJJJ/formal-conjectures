/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2847 : Family 10 := level10.get ⟨1195,by decide⟩
def sourceMap2847 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2847 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2847_checked : acceptsGraphIso
    (source (graph core2847) (root 10) 0 4) DegreeTwoThreeSpectrum6368.graph sourceMap2847=true := by decide +kernel
theorem fusedMap2847_checked : acceptsGraphIso
    (fused (graph core2847) (root 10) 0 4) DegreeTwoThreeSpectrum6369.graph fusedMap2847=true := by decide +kernel
theorem certified2847 : Certified (graph core2847) (root 10) 0 4 :=
  of_native_maps core2847 DegreeTwoThreeSpectrum6368.graph DegreeTwoThreeSpectrum6369.graph
    sourceMap2847 fusedMap2847 sourceMap2847_checked fusedMap2847_checked
    DegreeTwoThreeFiniteComparisons.comparison2847
#print axioms sourceMap2847_checked
#print axioms fusedMap2847_checked
#print axioms certified2847
def sourceMap2847swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2847swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2847swap_checked : acceptsGraphIso
    (source (graph core2847) (root 10) 4 0) DegreeTwoThreeSpectrum6368.graph sourceMap2847swap=true := by decide +kernel
theorem fusedMap2847swap_checked : acceptsGraphIso
    (fused (graph core2847) (root 10) 4 0) DegreeTwoThreeSpectrum6369.graph fusedMap2847swap=true := by decide +kernel
theorem certified2847swap : Certified (graph core2847) (root 10) 4 0 :=
  of_native_maps core2847 DegreeTwoThreeSpectrum6368.graph DegreeTwoThreeSpectrum6369.graph
    sourceMap2847swap fusedMap2847swap sourceMap2847swap_checked fusedMap2847swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2847
#print axioms sourceMap2847swap_checked
#print axioms fusedMap2847swap_checked
#print axioms certified2847swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
