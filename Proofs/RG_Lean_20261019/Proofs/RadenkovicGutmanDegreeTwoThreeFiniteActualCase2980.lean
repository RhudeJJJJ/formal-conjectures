/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2980 : Family 10 := level10.get ⟨1512,by decide⟩
def sourceMap2980 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2980 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2980_checked : acceptsGraphIso
    (source (graph core2980) (root 10) 0 4) DegreeTwoThreeSpectrum7021.graph sourceMap2980=true := by decide +kernel
theorem fusedMap2980_checked : acceptsGraphIso
    (fused (graph core2980) (root 10) 0 4) DegreeTwoThreeSpectrum7022.graph fusedMap2980=true := by decide +kernel
theorem certified2980 : Certified (graph core2980) (root 10) 0 4 :=
  of_native_maps core2980 DegreeTwoThreeSpectrum7021.graph DegreeTwoThreeSpectrum7022.graph
    sourceMap2980 fusedMap2980 sourceMap2980_checked fusedMap2980_checked
    DegreeTwoThreeFiniteComparisons.comparison2980
#print axioms sourceMap2980_checked
#print axioms fusedMap2980_checked
#print axioms certified2980
def sourceMap2980swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2980swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2980swap_checked : acceptsGraphIso
    (source (graph core2980) (root 10) 4 0) DegreeTwoThreeSpectrum7021.graph sourceMap2980swap=true := by decide +kernel
theorem fusedMap2980swap_checked : acceptsGraphIso
    (fused (graph core2980) (root 10) 4 0) DegreeTwoThreeSpectrum7022.graph fusedMap2980swap=true := by decide +kernel
theorem certified2980swap : Certified (graph core2980) (root 10) 4 0 :=
  of_native_maps core2980 DegreeTwoThreeSpectrum7021.graph DegreeTwoThreeSpectrum7022.graph
    sourceMap2980swap fusedMap2980swap sourceMap2980swap_checked fusedMap2980swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2980
#print axioms sourceMap2980swap_checked
#print axioms fusedMap2980swap_checked
#print axioms certified2980swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
