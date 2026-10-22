/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2910 : Family 10 := level10.get ⟨1340,by decide⟩
def sourceMap2910 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2910 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2910_checked : acceptsGraphIso
    (source (graph core2910) (root 10) 0 4) DegreeTwoThreeSpectrum6661.graph sourceMap2910=true := by decide +kernel
theorem fusedMap2910_checked : acceptsGraphIso
    (fused (graph core2910) (root 10) 0 4) DegreeTwoThreeSpectrum6662.graph fusedMap2910=true := by decide +kernel
theorem certified2910 : Certified (graph core2910) (root 10) 0 4 :=
  of_native_maps core2910 DegreeTwoThreeSpectrum6661.graph DegreeTwoThreeSpectrum6662.graph
    sourceMap2910 fusedMap2910 sourceMap2910_checked fusedMap2910_checked
    DegreeTwoThreeFiniteComparisons.comparison2910
#print axioms sourceMap2910_checked
#print axioms fusedMap2910_checked
#print axioms certified2910
def sourceMap2910swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2910swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2910swap_checked : acceptsGraphIso
    (source (graph core2910) (root 10) 4 0) DegreeTwoThreeSpectrum6661.graph sourceMap2910swap=true := by decide +kernel
theorem fusedMap2910swap_checked : acceptsGraphIso
    (fused (graph core2910) (root 10) 4 0) DegreeTwoThreeSpectrum6662.graph fusedMap2910swap=true := by decide +kernel
theorem certified2910swap : Certified (graph core2910) (root 10) 4 0 :=
  of_native_maps core2910 DegreeTwoThreeSpectrum6661.graph DegreeTwoThreeSpectrum6662.graph
    sourceMap2910swap fusedMap2910swap sourceMap2910swap_checked fusedMap2910swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2910
#print axioms sourceMap2910swap_checked
#print axioms fusedMap2910swap_checked
#print axioms certified2910swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
