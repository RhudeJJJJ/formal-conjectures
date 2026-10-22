/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2245 : Family 9 := level9.get ⟨130,by decide⟩
def sourceMap2245 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,6,7,1,2,3,4,5] (sourceLabel 9 0 4 v)
def fusedMap2245 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2245_checked : acceptsGraphIso
    (source (graph core2245) (root 9) 0 4) DegreeTwoThreeSpectrum4163.graph sourceMap2245=true := by decide +kernel
theorem fusedMap2245_checked : acceptsGraphIso
    (fused (graph core2245) (root 9) 0 4) DegreeTwoThreeSpectrum4165.graph fusedMap2245=true := by decide +kernel
theorem certified2245 : Certified (graph core2245) (root 9) 0 4 :=
  of_native_maps core2245 DegreeTwoThreeSpectrum4163.graph DegreeTwoThreeSpectrum4165.graph
    sourceMap2245 fusedMap2245 sourceMap2245_checked fusedMap2245_checked
    DegreeTwoThreeFiniteComparisons.comparison2245
#print axioms sourceMap2245_checked
#print axioms fusedMap2245_checked
#print axioms certified2245
def sourceMap2245swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,6,1,2,3,4,5,7] (sourceLabel 9 4 0 v)
def fusedMap2245swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2245swap_checked : acceptsGraphIso
    (source (graph core2245) (root 9) 4 0) DegreeTwoThreeSpectrum4163.graph sourceMap2245swap=true := by decide +kernel
theorem fusedMap2245swap_checked : acceptsGraphIso
    (fused (graph core2245) (root 9) 4 0) DegreeTwoThreeSpectrum4165.graph fusedMap2245swap=true := by decide +kernel
theorem certified2245swap : Certified (graph core2245) (root 9) 4 0 :=
  of_native_maps core2245 DegreeTwoThreeSpectrum4163.graph DegreeTwoThreeSpectrum4165.graph
    sourceMap2245swap fusedMap2245swap sourceMap2245swap_checked fusedMap2245swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2245
#print axioms sourceMap2245swap_checked
#print axioms fusedMap2245swap_checked
#print axioms certified2245swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
