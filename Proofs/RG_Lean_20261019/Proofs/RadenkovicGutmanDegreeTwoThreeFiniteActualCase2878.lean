/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2878 : Family 10 := level10.get ⟨1266,by decide⟩
def sourceMap2878 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2878 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2878_checked : acceptsGraphIso
    (source (graph core2878) (root 10) 0 4) DegreeTwoThreeSpectrum6520.graph sourceMap2878=true := by decide +kernel
theorem fusedMap2878_checked : acceptsGraphIso
    (fused (graph core2878) (root 10) 0 4) DegreeTwoThreeSpectrum6521.graph fusedMap2878=true := by decide +kernel
theorem certified2878 : Certified (graph core2878) (root 10) 0 4 :=
  of_native_maps core2878 DegreeTwoThreeSpectrum6520.graph DegreeTwoThreeSpectrum6521.graph
    sourceMap2878 fusedMap2878 sourceMap2878_checked fusedMap2878_checked
    DegreeTwoThreeFiniteComparisons.comparison2878
#print axioms sourceMap2878_checked
#print axioms fusedMap2878_checked
#print axioms certified2878
def sourceMap2878swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2878swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2878swap_checked : acceptsGraphIso
    (source (graph core2878) (root 10) 4 0) DegreeTwoThreeSpectrum6520.graph sourceMap2878swap=true := by decide +kernel
theorem fusedMap2878swap_checked : acceptsGraphIso
    (fused (graph core2878) (root 10) 4 0) DegreeTwoThreeSpectrum6521.graph fusedMap2878swap=true := by decide +kernel
theorem certified2878swap : Certified (graph core2878) (root 10) 4 0 :=
  of_native_maps core2878 DegreeTwoThreeSpectrum6520.graph DegreeTwoThreeSpectrum6521.graph
    sourceMap2878swap fusedMap2878swap sourceMap2878swap_checked fusedMap2878swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2878
#print axioms sourceMap2878swap_checked
#print axioms fusedMap2878swap_checked
#print axioms certified2878swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
