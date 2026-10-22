/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2871 : Family 10 := level10.get ⟨1251,by decide⟩
def sourceMap2871 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2871 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2871_checked : acceptsGraphIso
    (source (graph core2871) (root 10) 0 4) DegreeTwoThreeSpectrum6490.graph sourceMap2871=true := by decide +kernel
theorem fusedMap2871_checked : acceptsGraphIso
    (fused (graph core2871) (root 10) 0 4) DegreeTwoThreeSpectrum6491.graph fusedMap2871=true := by decide +kernel
theorem certified2871 : Certified (graph core2871) (root 10) 0 4 :=
  of_native_maps core2871 DegreeTwoThreeSpectrum6490.graph DegreeTwoThreeSpectrum6491.graph
    sourceMap2871 fusedMap2871 sourceMap2871_checked fusedMap2871_checked
    DegreeTwoThreeFiniteComparisons.comparison2871
#print axioms sourceMap2871_checked
#print axioms fusedMap2871_checked
#print axioms certified2871
def sourceMap2871swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2871swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2871swap_checked : acceptsGraphIso
    (source (graph core2871) (root 10) 4 0) DegreeTwoThreeSpectrum6490.graph sourceMap2871swap=true := by decide +kernel
theorem fusedMap2871swap_checked : acceptsGraphIso
    (fused (graph core2871) (root 10) 4 0) DegreeTwoThreeSpectrum6491.graph fusedMap2871swap=true := by decide +kernel
theorem certified2871swap : Certified (graph core2871) (root 10) 4 0 :=
  of_native_maps core2871 DegreeTwoThreeSpectrum6490.graph DegreeTwoThreeSpectrum6491.graph
    sourceMap2871swap fusedMap2871swap sourceMap2871swap_checked fusedMap2871swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2871
#print axioms sourceMap2871swap_checked
#print axioms fusedMap2871swap_checked
#print axioms certified2871swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
