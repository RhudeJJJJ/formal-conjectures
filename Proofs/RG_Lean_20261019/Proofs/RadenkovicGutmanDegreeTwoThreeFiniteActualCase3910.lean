/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3910 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap3910 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3910 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3910_checked : acceptsGraphIso
    (source (graph core3910) (root 8) 1 4) DegreeTwoThreeSpectrum4803.graph sourceMap3910=true := by decide +kernel
theorem fusedMap3910_checked : acceptsGraphIso
    (fused (graph core3910) (root 8) 1 4) DegreeTwoThreeSpectrum4416.graph fusedMap3910=true := by decide +kernel
theorem certified3910 : Certified (graph core3910) (root 8) 1 4 :=
  of_native_maps core3910 DegreeTwoThreeSpectrum4803.graph DegreeTwoThreeSpectrum4416.graph
    sourceMap3910 fusedMap3910 sourceMap3910_checked fusedMap3910_checked
    DegreeTwoThreeFiniteComparisons.comparison3910
#print axioms sourceMap3910_checked
#print axioms fusedMap3910_checked
#print axioms certified3910
def sourceMap3910swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3910swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3910swap_checked : acceptsGraphIso
    (source (graph core3910) (root 8) 4 1) DegreeTwoThreeSpectrum4803.graph sourceMap3910swap=true := by decide +kernel
theorem fusedMap3910swap_checked : acceptsGraphIso
    (fused (graph core3910) (root 8) 4 1) DegreeTwoThreeSpectrum4416.graph fusedMap3910swap=true := by decide +kernel
theorem certified3910swap : Certified (graph core3910) (root 8) 4 1 :=
  of_native_maps core3910 DegreeTwoThreeSpectrum4803.graph DegreeTwoThreeSpectrum4416.graph
    sourceMap3910swap fusedMap3910swap sourceMap3910swap_checked fusedMap3910swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3910
#print axioms sourceMap3910swap_checked
#print axioms fusedMap3910swap_checked
#print axioms certified3910swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
