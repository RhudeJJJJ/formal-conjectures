/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2220 : Family 9 := level9.get ⟨37,by decide⟩
def sourceMap2220 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,7,8,2,3,4,5,6] (sourceLabel 9 0 4 v)
def fusedMap2220 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2220_checked : acceptsGraphIso
    (source (graph core2220) (root 9) 0 4) DegreeTwoThreeSpectrum4164.graph sourceMap2220=true := by decide +kernel
theorem fusedMap2220_checked : acceptsGraphIso
    (fused (graph core2220) (root 9) 0 4) DegreeTwoThreeSpectrum3886.graph fusedMap2220=true := by decide +kernel
theorem certified2220 : Certified (graph core2220) (root 9) 0 4 :=
  of_native_maps core2220 DegreeTwoThreeSpectrum4164.graph DegreeTwoThreeSpectrum3886.graph
    sourceMap2220 fusedMap2220 sourceMap2220_checked fusedMap2220_checked
    DegreeTwoThreeFiniteComparisons.comparison2220
#print axioms sourceMap2220_checked
#print axioms fusedMap2220_checked
#print axioms certified2220
def sourceMap2220swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,7,2,3,4,5,6,8] (sourceLabel 9 4 0 v)
def fusedMap2220swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2220swap_checked : acceptsGraphIso
    (source (graph core2220) (root 9) 4 0) DegreeTwoThreeSpectrum4164.graph sourceMap2220swap=true := by decide +kernel
theorem fusedMap2220swap_checked : acceptsGraphIso
    (fused (graph core2220) (root 9) 4 0) DegreeTwoThreeSpectrum3886.graph fusedMap2220swap=true := by decide +kernel
theorem certified2220swap : Certified (graph core2220) (root 9) 4 0 :=
  of_native_maps core2220 DegreeTwoThreeSpectrum4164.graph DegreeTwoThreeSpectrum3886.graph
    sourceMap2220swap fusedMap2220swap sourceMap2220swap_checked fusedMap2220swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2220
#print axioms sourceMap2220swap_checked
#print axioms fusedMap2220swap_checked
#print axioms certified2220swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
