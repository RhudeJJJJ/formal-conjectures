/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2244 : Family 9 := level9.get ⟨128,by decide⟩
def sourceMap2244 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2244 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2244_checked : acceptsGraphIso
    (source (graph core2244) (root 9) 0 4) DegreeTwoThreeSpectrum4161.graph sourceMap2244=true := by decide +kernel
theorem fusedMap2244_checked : acceptsGraphIso
    (fused (graph core2244) (root 9) 0 4) DegreeTwoThreeSpectrum4162.graph fusedMap2244=true := by decide +kernel
theorem certified2244 : Certified (graph core2244) (root 9) 0 4 :=
  of_native_maps core2244 DegreeTwoThreeSpectrum4161.graph DegreeTwoThreeSpectrum4162.graph
    sourceMap2244 fusedMap2244 sourceMap2244_checked fusedMap2244_checked
    DegreeTwoThreeFiniteComparisons.comparison2244
#print axioms sourceMap2244_checked
#print axioms fusedMap2244_checked
#print axioms certified2244
def sourceMap2244swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2244swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2244swap_checked : acceptsGraphIso
    (source (graph core2244) (root 9) 4 0) DegreeTwoThreeSpectrum4161.graph sourceMap2244swap=true := by decide +kernel
theorem fusedMap2244swap_checked : acceptsGraphIso
    (fused (graph core2244) (root 9) 4 0) DegreeTwoThreeSpectrum4162.graph fusedMap2244swap=true := by decide +kernel
theorem certified2244swap : Certified (graph core2244) (root 9) 4 0 :=
  of_native_maps core2244 DegreeTwoThreeSpectrum4161.graph DegreeTwoThreeSpectrum4162.graph
    sourceMap2244swap fusedMap2244swap sourceMap2244swap_checked fusedMap2244swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2244
#print axioms sourceMap2244swap_checked
#print axioms fusedMap2244swap_checked
#print axioms certified2244swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
