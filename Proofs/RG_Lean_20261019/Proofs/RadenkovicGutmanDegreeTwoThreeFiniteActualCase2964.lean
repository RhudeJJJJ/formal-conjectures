/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2964 : Family 10 := level10.get ⟨1466,by decide⟩
def sourceMap2964 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2964 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2964_checked : acceptsGraphIso
    (source (graph core2964) (root 10) 0 4) DegreeTwoThreeSpectrum6944.graph sourceMap2964=true := by decide +kernel
theorem fusedMap2964_checked : acceptsGraphIso
    (fused (graph core2964) (root 10) 0 4) DegreeTwoThreeSpectrum6945.graph fusedMap2964=true := by decide +kernel
theorem certified2964 : Certified (graph core2964) (root 10) 0 4 :=
  of_native_maps core2964 DegreeTwoThreeSpectrum6944.graph DegreeTwoThreeSpectrum6945.graph
    sourceMap2964 fusedMap2964 sourceMap2964_checked fusedMap2964_checked
    DegreeTwoThreeFiniteComparisons.comparison2964
#print axioms sourceMap2964_checked
#print axioms fusedMap2964_checked
#print axioms certified2964
def sourceMap2964swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2964swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2964swap_checked : acceptsGraphIso
    (source (graph core2964) (root 10) 4 0) DegreeTwoThreeSpectrum6944.graph sourceMap2964swap=true := by decide +kernel
theorem fusedMap2964swap_checked : acceptsGraphIso
    (fused (graph core2964) (root 10) 4 0) DegreeTwoThreeSpectrum6945.graph fusedMap2964swap=true := by decide +kernel
theorem certified2964swap : Certified (graph core2964) (root 10) 4 0 :=
  of_native_maps core2964 DegreeTwoThreeSpectrum6944.graph DegreeTwoThreeSpectrum6945.graph
    sourceMap2964swap fusedMap2964swap sourceMap2964swap_checked fusedMap2964swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2964
#print axioms sourceMap2964swap_checked
#print axioms fusedMap2964swap_checked
#print axioms certified2964swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
