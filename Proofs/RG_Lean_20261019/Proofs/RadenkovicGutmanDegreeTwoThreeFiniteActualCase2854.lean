/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2854 : Family 10 := level10.get ⟨1208,by decide⟩
def sourceMap2854 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2854 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2854_checked : acceptsGraphIso
    (source (graph core2854) (root 10) 0 4) DegreeTwoThreeSpectrum6390.graph sourceMap2854=true := by decide +kernel
theorem fusedMap2854_checked : acceptsGraphIso
    (fused (graph core2854) (root 10) 0 4) DegreeTwoThreeSpectrum6391.graph fusedMap2854=true := by decide +kernel
theorem certified2854 : Certified (graph core2854) (root 10) 0 4 :=
  of_native_maps core2854 DegreeTwoThreeSpectrum6390.graph DegreeTwoThreeSpectrum6391.graph
    sourceMap2854 fusedMap2854 sourceMap2854_checked fusedMap2854_checked
    DegreeTwoThreeFiniteComparisons.comparison2854
#print axioms sourceMap2854_checked
#print axioms fusedMap2854_checked
#print axioms certified2854
def sourceMap2854swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2854swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2854swap_checked : acceptsGraphIso
    (source (graph core2854) (root 10) 4 0) DegreeTwoThreeSpectrum6390.graph sourceMap2854swap=true := by decide +kernel
theorem fusedMap2854swap_checked : acceptsGraphIso
    (fused (graph core2854) (root 10) 4 0) DegreeTwoThreeSpectrum6391.graph fusedMap2854swap=true := by decide +kernel
theorem certified2854swap : Certified (graph core2854) (root 10) 4 0 :=
  of_native_maps core2854 DegreeTwoThreeSpectrum6390.graph DegreeTwoThreeSpectrum6391.graph
    sourceMap2854swap fusedMap2854swap sourceMap2854swap_checked fusedMap2854swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2854
#print axioms sourceMap2854swap_checked
#print axioms fusedMap2854swap_checked
#print axioms certified2854swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
