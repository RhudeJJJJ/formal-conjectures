/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2903 : Family 10 := level10.get ⟨1329,by decide⟩
def sourceMap2903 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2903 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2903_checked : acceptsGraphIso
    (source (graph core2903) (root 10) 0 4) DegreeTwoThreeSpectrum6639.graph sourceMap2903=true := by decide +kernel
theorem fusedMap2903_checked : acceptsGraphIso
    (fused (graph core2903) (root 10) 0 4) DegreeTwoThreeSpectrum6640.graph fusedMap2903=true := by decide +kernel
theorem certified2903 : Certified (graph core2903) (root 10) 0 4 :=
  of_native_maps core2903 DegreeTwoThreeSpectrum6639.graph DegreeTwoThreeSpectrum6640.graph
    sourceMap2903 fusedMap2903 sourceMap2903_checked fusedMap2903_checked
    DegreeTwoThreeFiniteComparisons.comparison2903
#print axioms sourceMap2903_checked
#print axioms fusedMap2903_checked
#print axioms certified2903
def sourceMap2903swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2903swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2903swap_checked : acceptsGraphIso
    (source (graph core2903) (root 10) 4 0) DegreeTwoThreeSpectrum6639.graph sourceMap2903swap=true := by decide +kernel
theorem fusedMap2903swap_checked : acceptsGraphIso
    (fused (graph core2903) (root 10) 4 0) DegreeTwoThreeSpectrum6640.graph fusedMap2903swap=true := by decide +kernel
theorem certified2903swap : Certified (graph core2903) (root 10) 4 0 :=
  of_native_maps core2903 DegreeTwoThreeSpectrum6639.graph DegreeTwoThreeSpectrum6640.graph
    sourceMap2903swap fusedMap2903swap sourceMap2903swap_checked fusedMap2903swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2903
#print axioms sourceMap2903swap_checked
#print axioms fusedMap2903swap_checked
#print axioms certified2903swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
