/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2978 : Family 10 := level10.get ⟨1502,by decide⟩
def sourceMap2978 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2978 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2978_checked : acceptsGraphIso
    (source (graph core2978) (root 10) 0 4) DegreeTwoThreeSpectrum7007.graph sourceMap2978=true := by decide +kernel
theorem fusedMap2978_checked : acceptsGraphIso
    (fused (graph core2978) (root 10) 0 4) DegreeTwoThreeSpectrum7008.graph fusedMap2978=true := by decide +kernel
theorem certified2978 : Certified (graph core2978) (root 10) 0 4 :=
  of_native_maps core2978 DegreeTwoThreeSpectrum7007.graph DegreeTwoThreeSpectrum7008.graph
    sourceMap2978 fusedMap2978 sourceMap2978_checked fusedMap2978_checked
    DegreeTwoThreeFiniteComparisons.comparison2978
#print axioms sourceMap2978_checked
#print axioms fusedMap2978_checked
#print axioms certified2978
def sourceMap2978swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2978swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2978swap_checked : acceptsGraphIso
    (source (graph core2978) (root 10) 4 0) DegreeTwoThreeSpectrum7007.graph sourceMap2978swap=true := by decide +kernel
theorem fusedMap2978swap_checked : acceptsGraphIso
    (fused (graph core2978) (root 10) 4 0) DegreeTwoThreeSpectrum7008.graph fusedMap2978swap=true := by decide +kernel
theorem certified2978swap : Certified (graph core2978) (root 10) 4 0 :=
  of_native_maps core2978 DegreeTwoThreeSpectrum7007.graph DegreeTwoThreeSpectrum7008.graph
    sourceMap2978swap fusedMap2978swap sourceMap2978swap_checked fusedMap2978swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2978
#print axioms sourceMap2978swap_checked
#print axioms fusedMap2978swap_checked
#print axioms certified2978swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
