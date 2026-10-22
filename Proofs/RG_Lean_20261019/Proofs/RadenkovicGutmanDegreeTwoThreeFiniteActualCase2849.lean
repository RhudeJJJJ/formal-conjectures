/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2849 : Family 10 := level10.get ⟨1198,by decide⟩
def sourceMap2849 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2849 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2849_checked : acceptsGraphIso
    (source (graph core2849) (root 10) 0 4) DegreeTwoThreeSpectrum6372.graph sourceMap2849=true := by decide +kernel
theorem fusedMap2849_checked : acceptsGraphIso
    (fused (graph core2849) (root 10) 0 4) DegreeTwoThreeSpectrum6373.graph fusedMap2849=true := by decide +kernel
theorem certified2849 : Certified (graph core2849) (root 10) 0 4 :=
  of_native_maps core2849 DegreeTwoThreeSpectrum6372.graph DegreeTwoThreeSpectrum6373.graph
    sourceMap2849 fusedMap2849 sourceMap2849_checked fusedMap2849_checked
    DegreeTwoThreeFiniteComparisons.comparison2849
#print axioms sourceMap2849_checked
#print axioms fusedMap2849_checked
#print axioms certified2849
def sourceMap2849swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2849swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2849swap_checked : acceptsGraphIso
    (source (graph core2849) (root 10) 4 0) DegreeTwoThreeSpectrum6372.graph sourceMap2849swap=true := by decide +kernel
theorem fusedMap2849swap_checked : acceptsGraphIso
    (fused (graph core2849) (root 10) 4 0) DegreeTwoThreeSpectrum6373.graph fusedMap2849swap=true := by decide +kernel
theorem certified2849swap : Certified (graph core2849) (root 10) 4 0 :=
  of_native_maps core2849 DegreeTwoThreeSpectrum6372.graph DegreeTwoThreeSpectrum6373.graph
    sourceMap2849swap fusedMap2849swap sourceMap2849swap_checked fusedMap2849swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2849
#print axioms sourceMap2849swap_checked
#print axioms fusedMap2849swap_checked
#print axioms certified2849swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
