/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2940 : Family 10 := level10.get ⟨1413,by decide⟩
def sourceMap2940 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2940 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2940_checked : acceptsGraphIso
    (source (graph core2940) (root 10) 0 4) DegreeTwoThreeSpectrum6858.graph sourceMap2940=true := by decide +kernel
theorem fusedMap2940_checked : acceptsGraphIso
    (fused (graph core2940) (root 10) 0 4) DegreeTwoThreeSpectrum6859.graph fusedMap2940=true := by decide +kernel
theorem certified2940 : Certified (graph core2940) (root 10) 0 4 :=
  of_native_maps core2940 DegreeTwoThreeSpectrum6858.graph DegreeTwoThreeSpectrum6859.graph
    sourceMap2940 fusedMap2940 sourceMap2940_checked fusedMap2940_checked
    DegreeTwoThreeFiniteComparisons.comparison2940
#print axioms sourceMap2940_checked
#print axioms fusedMap2940_checked
#print axioms certified2940
def sourceMap2940swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2940swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2940swap_checked : acceptsGraphIso
    (source (graph core2940) (root 10) 4 0) DegreeTwoThreeSpectrum6858.graph sourceMap2940swap=true := by decide +kernel
theorem fusedMap2940swap_checked : acceptsGraphIso
    (fused (graph core2940) (root 10) 4 0) DegreeTwoThreeSpectrum6859.graph fusedMap2940swap=true := by decide +kernel
theorem certified2940swap : Certified (graph core2940) (root 10) 4 0 :=
  of_native_maps core2940 DegreeTwoThreeSpectrum6858.graph DegreeTwoThreeSpectrum6859.graph
    sourceMap2940swap fusedMap2940swap sourceMap2940swap_checked fusedMap2940swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2940
#print axioms sourceMap2940swap_checked
#print axioms fusedMap2940swap_checked
#print axioms certified2940swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
