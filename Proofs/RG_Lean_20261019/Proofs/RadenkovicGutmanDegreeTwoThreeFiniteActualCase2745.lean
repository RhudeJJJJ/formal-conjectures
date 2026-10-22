/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2745 : Family 10 := level10.get ⟨938,by decide⟩
def sourceMap2745 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2745 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2745_checked : acceptsGraphIso
    (source (graph core2745) (root 10) 0 4) DegreeTwoThreeSpectrum7020.graph sourceMap2745=true := by decide +kernel
theorem fusedMap2745_checked : acceptsGraphIso
    (fused (graph core2745) (root 10) 0 4) DegreeTwoThreeSpectrum5834.graph fusedMap2745=true := by decide +kernel
theorem certified2745 : Certified (graph core2745) (root 10) 0 4 :=
  of_native_maps core2745 DegreeTwoThreeSpectrum7020.graph DegreeTwoThreeSpectrum5834.graph
    sourceMap2745 fusedMap2745 sourceMap2745_checked fusedMap2745_checked
    DegreeTwoThreeFiniteComparisons.comparison2745
#print axioms sourceMap2745_checked
#print axioms fusedMap2745_checked
#print axioms certified2745
def sourceMap2745swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2745swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2745swap_checked : acceptsGraphIso
    (source (graph core2745) (root 10) 4 0) DegreeTwoThreeSpectrum7020.graph sourceMap2745swap=true := by decide +kernel
theorem fusedMap2745swap_checked : acceptsGraphIso
    (fused (graph core2745) (root 10) 4 0) DegreeTwoThreeSpectrum5834.graph fusedMap2745swap=true := by decide +kernel
theorem certified2745swap : Certified (graph core2745) (root 10) 4 0 :=
  of_native_maps core2745 DegreeTwoThreeSpectrum7020.graph DegreeTwoThreeSpectrum5834.graph
    sourceMap2745swap fusedMap2745swap sourceMap2745swap_checked fusedMap2745swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2745
#print axioms sourceMap2745swap_checked
#print axioms fusedMap2745swap_checked
#print axioms certified2745swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
