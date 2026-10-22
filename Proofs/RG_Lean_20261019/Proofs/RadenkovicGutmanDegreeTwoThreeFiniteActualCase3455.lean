/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3455 : Family 9 := level9.get ⟨631,by decide⟩
def sourceMap3455 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3455 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3455_checked : acceptsGraphIso
    (source (graph core3455) (root 9) 0 5) DegreeTwoThreeSpectrum6471.graph sourceMap3455=true := by decide +kernel
theorem fusedMap3455_checked : acceptsGraphIso
    (fused (graph core3455) (root 9) 0 5) DegreeTwoThreeSpectrum6472.graph fusedMap3455=true := by decide +kernel
theorem certified3455 : Certified (graph core3455) (root 9) 0 5 :=
  of_native_maps core3455 DegreeTwoThreeSpectrum6471.graph DegreeTwoThreeSpectrum6472.graph
    sourceMap3455 fusedMap3455 sourceMap3455_checked fusedMap3455_checked
    DegreeTwoThreeFiniteComparisons.comparison3455
#print axioms sourceMap3455_checked
#print axioms fusedMap3455_checked
#print axioms certified3455
def sourceMap3455swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3455swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3455swap_checked : acceptsGraphIso
    (source (graph core3455) (root 9) 5 0) DegreeTwoThreeSpectrum6471.graph sourceMap3455swap=true := by decide +kernel
theorem fusedMap3455swap_checked : acceptsGraphIso
    (fused (graph core3455) (root 9) 5 0) DegreeTwoThreeSpectrum6472.graph fusedMap3455swap=true := by decide +kernel
theorem certified3455swap : Certified (graph core3455) (root 9) 5 0 :=
  of_native_maps core3455 DegreeTwoThreeSpectrum6471.graph DegreeTwoThreeSpectrum6472.graph
    sourceMap3455swap fusedMap3455swap sourceMap3455swap_checked fusedMap3455swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3455
#print axioms sourceMap3455swap_checked
#print axioms fusedMap3455swap_checked
#print axioms certified3455swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
