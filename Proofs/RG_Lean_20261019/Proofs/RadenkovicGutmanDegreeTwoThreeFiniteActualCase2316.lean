/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2316 : Family 9 := level9.get ⟨339,by decide⟩
def sourceMap2316 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2316 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2316_checked : acceptsGraphIso
    (source (graph core2316) (root 9) 0 4) DegreeTwoThreeSpectrum4227.graph sourceMap2316=true := by decide +kernel
theorem fusedMap2316_checked : acceptsGraphIso
    (fused (graph core2316) (root 9) 0 4) DegreeTwoThreeSpectrum4228.graph fusedMap2316=true := by decide +kernel
theorem certified2316 : Certified (graph core2316) (root 9) 0 4 :=
  of_native_maps core2316 DegreeTwoThreeSpectrum4227.graph DegreeTwoThreeSpectrum4228.graph
    sourceMap2316 fusedMap2316 sourceMap2316_checked fusedMap2316_checked
    DegreeTwoThreeFiniteComparisons.comparison2316
#print axioms sourceMap2316_checked
#print axioms fusedMap2316_checked
#print axioms certified2316
def sourceMap2316swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2316swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2316swap_checked : acceptsGraphIso
    (source (graph core2316) (root 9) 4 0) DegreeTwoThreeSpectrum4227.graph sourceMap2316swap=true := by decide +kernel
theorem fusedMap2316swap_checked : acceptsGraphIso
    (fused (graph core2316) (root 9) 4 0) DegreeTwoThreeSpectrum4228.graph fusedMap2316swap=true := by decide +kernel
theorem certified2316swap : Certified (graph core2316) (root 9) 4 0 :=
  of_native_maps core2316 DegreeTwoThreeSpectrum4227.graph DegreeTwoThreeSpectrum4228.graph
    sourceMap2316swap fusedMap2316swap sourceMap2316swap_checked fusedMap2316swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2316
#print axioms sourceMap2316swap_checked
#print axioms fusedMap2316swap_checked
#print axioms certified2316swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
