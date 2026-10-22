/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2898 : Family 10 := level10.get ⟨1314,by decide⟩
def sourceMap2898 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2898 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2898_checked : acceptsGraphIso
    (source (graph core2898) (root 10) 0 4) DegreeTwoThreeSpectrum6614.graph sourceMap2898=true := by decide +kernel
theorem fusedMap2898_checked : acceptsGraphIso
    (fused (graph core2898) (root 10) 0 4) DegreeTwoThreeSpectrum6615.graph fusedMap2898=true := by decide +kernel
theorem certified2898 : Certified (graph core2898) (root 10) 0 4 :=
  of_native_maps core2898 DegreeTwoThreeSpectrum6614.graph DegreeTwoThreeSpectrum6615.graph
    sourceMap2898 fusedMap2898 sourceMap2898_checked fusedMap2898_checked
    DegreeTwoThreeFiniteComparisons.comparison2898
#print axioms sourceMap2898_checked
#print axioms fusedMap2898_checked
#print axioms certified2898
def sourceMap2898swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2898swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2898swap_checked : acceptsGraphIso
    (source (graph core2898) (root 10) 4 0) DegreeTwoThreeSpectrum6614.graph sourceMap2898swap=true := by decide +kernel
theorem fusedMap2898swap_checked : acceptsGraphIso
    (fused (graph core2898) (root 10) 4 0) DegreeTwoThreeSpectrum6615.graph fusedMap2898swap=true := by decide +kernel
theorem certified2898swap : Certified (graph core2898) (root 10) 4 0 :=
  of_native_maps core2898 DegreeTwoThreeSpectrum6614.graph DegreeTwoThreeSpectrum6615.graph
    sourceMap2898swap fusedMap2898swap sourceMap2898swap_checked fusedMap2898swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2898
#print axioms sourceMap2898swap_checked
#print axioms fusedMap2898swap_checked
#print axioms certified2898swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
