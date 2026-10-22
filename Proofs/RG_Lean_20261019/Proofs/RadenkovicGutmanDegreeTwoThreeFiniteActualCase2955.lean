/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2955 : Family 10 := level10.get ⟨1446,by decide⟩
def sourceMap2955 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2955 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2955_checked : acceptsGraphIso
    (source (graph core2955) (root 10) 0 4) DegreeTwoThreeSpectrum6910.graph sourceMap2955=true := by decide +kernel
theorem fusedMap2955_checked : acceptsGraphIso
    (fused (graph core2955) (root 10) 0 4) DegreeTwoThreeSpectrum6911.graph fusedMap2955=true := by decide +kernel
theorem certified2955 : Certified (graph core2955) (root 10) 0 4 :=
  of_native_maps core2955 DegreeTwoThreeSpectrum6910.graph DegreeTwoThreeSpectrum6911.graph
    sourceMap2955 fusedMap2955 sourceMap2955_checked fusedMap2955_checked
    DegreeTwoThreeFiniteComparisons.comparison2955
#print axioms sourceMap2955_checked
#print axioms fusedMap2955_checked
#print axioms certified2955
def sourceMap2955swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2955swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2955swap_checked : acceptsGraphIso
    (source (graph core2955) (root 10) 4 0) DegreeTwoThreeSpectrum6910.graph sourceMap2955swap=true := by decide +kernel
theorem fusedMap2955swap_checked : acceptsGraphIso
    (fused (graph core2955) (root 10) 4 0) DegreeTwoThreeSpectrum6911.graph fusedMap2955swap=true := by decide +kernel
theorem certified2955swap : Certified (graph core2955) (root 10) 4 0 :=
  of_native_maps core2955 DegreeTwoThreeSpectrum6910.graph DegreeTwoThreeSpectrum6911.graph
    sourceMap2955swap fusedMap2955swap sourceMap2955swap_checked fusedMap2955swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2955
#print axioms sourceMap2955swap_checked
#print axioms fusedMap2955swap_checked
#print axioms certified2955swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
