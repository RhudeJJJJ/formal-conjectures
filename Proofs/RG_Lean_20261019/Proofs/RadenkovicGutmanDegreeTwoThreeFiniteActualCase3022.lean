/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3022 : Family 10 := level10.get ⟨1621,by decide⟩
def sourceMap3022 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3022 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3022_checked : acceptsGraphIso
    (source (graph core3022) (root 10) 0 4) DegreeTwoThreeSpectrum7178.graph sourceMap3022=true := by decide +kernel
theorem fusedMap3022_checked : acceptsGraphIso
    (fused (graph core3022) (root 10) 0 4) DegreeTwoThreeSpectrum6179.graph fusedMap3022=true := by decide +kernel
theorem certified3022 : Certified (graph core3022) (root 10) 0 4 :=
  of_native_maps core3022 DegreeTwoThreeSpectrum7178.graph DegreeTwoThreeSpectrum6179.graph
    sourceMap3022 fusedMap3022 sourceMap3022_checked fusedMap3022_checked
    DegreeTwoThreeFiniteComparisons.comparison3022
#print axioms sourceMap3022_checked
#print axioms fusedMap3022_checked
#print axioms certified3022
def sourceMap3022swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3022swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3022swap_checked : acceptsGraphIso
    (source (graph core3022) (root 10) 4 0) DegreeTwoThreeSpectrum7178.graph sourceMap3022swap=true := by decide +kernel
theorem fusedMap3022swap_checked : acceptsGraphIso
    (fused (graph core3022) (root 10) 4 0) DegreeTwoThreeSpectrum6179.graph fusedMap3022swap=true := by decide +kernel
theorem certified3022swap : Certified (graph core3022) (root 10) 4 0 :=
  of_native_maps core3022 DegreeTwoThreeSpectrum7178.graph DegreeTwoThreeSpectrum6179.graph
    sourceMap3022swap fusedMap3022swap sourceMap3022swap_checked fusedMap3022swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3022
#print axioms sourceMap3022swap_checked
#print axioms fusedMap3022swap_checked
#print axioms certified3022swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
