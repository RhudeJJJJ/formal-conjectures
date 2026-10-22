/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2296 : Family 9 := level9.get ⟨283,by decide⟩
def sourceMap2296 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2296 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2296_checked : acceptsGraphIso
    (source (graph core2296) (root 9) 0 4) DegreeTwoThreeSpectrum4623.graph sourceMap2296=true := by decide +kernel
theorem fusedMap2296_checked : acceptsGraphIso
    (fused (graph core2296) (root 9) 0 4) DegreeTwoThreeSpectrum4104.graph fusedMap2296=true := by decide +kernel
theorem certified2296 : Certified (graph core2296) (root 9) 0 4 :=
  of_native_maps core2296 DegreeTwoThreeSpectrum4623.graph DegreeTwoThreeSpectrum4104.graph
    sourceMap2296 fusedMap2296 sourceMap2296_checked fusedMap2296_checked
    DegreeTwoThreeFiniteComparisons.comparison2296
#print axioms sourceMap2296_checked
#print axioms fusedMap2296_checked
#print axioms certified2296
def sourceMap2296swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2296swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2296swap_checked : acceptsGraphIso
    (source (graph core2296) (root 9) 4 0) DegreeTwoThreeSpectrum4623.graph sourceMap2296swap=true := by decide +kernel
theorem fusedMap2296swap_checked : acceptsGraphIso
    (fused (graph core2296) (root 9) 4 0) DegreeTwoThreeSpectrum4104.graph fusedMap2296swap=true := by decide +kernel
theorem certified2296swap : Certified (graph core2296) (root 9) 4 0 :=
  of_native_maps core2296 DegreeTwoThreeSpectrum4623.graph DegreeTwoThreeSpectrum4104.graph
    sourceMap2296swap fusedMap2296swap sourceMap2296swap_checked fusedMap2296swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2296
#print axioms sourceMap2296swap_checked
#print axioms fusedMap2296swap_checked
#print axioms certified2296swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
