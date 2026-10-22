/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3908 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap3908 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3908 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3908_checked : acceptsGraphIso
    (source (graph core3908) (root 8) 1 4) DegreeTwoThreeSpectrum4793.graph sourceMap3908=true := by decide +kernel
theorem fusedMap3908_checked : acceptsGraphIso
    (fused (graph core3908) (root 8) 1 4) DegreeTwoThreeSpectrum4400.graph fusedMap3908=true := by decide +kernel
theorem certified3908 : Certified (graph core3908) (root 8) 1 4 :=
  of_native_maps core3908 DegreeTwoThreeSpectrum4793.graph DegreeTwoThreeSpectrum4400.graph
    sourceMap3908 fusedMap3908 sourceMap3908_checked fusedMap3908_checked
    DegreeTwoThreeFiniteComparisons.comparison3908
#print axioms sourceMap3908_checked
#print axioms fusedMap3908_checked
#print axioms certified3908
def sourceMap3908swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3908swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3908swap_checked : acceptsGraphIso
    (source (graph core3908) (root 8) 4 1) DegreeTwoThreeSpectrum4793.graph sourceMap3908swap=true := by decide +kernel
theorem fusedMap3908swap_checked : acceptsGraphIso
    (fused (graph core3908) (root 8) 4 1) DegreeTwoThreeSpectrum4400.graph fusedMap3908swap=true := by decide +kernel
theorem certified3908swap : Certified (graph core3908) (root 8) 4 1 :=
  of_native_maps core3908 DegreeTwoThreeSpectrum4793.graph DegreeTwoThreeSpectrum4400.graph
    sourceMap3908swap fusedMap3908swap sourceMap3908swap_checked fusedMap3908swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3908
#print axioms sourceMap3908swap_checked
#print axioms fusedMap3908swap_checked
#print axioms certified3908swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
