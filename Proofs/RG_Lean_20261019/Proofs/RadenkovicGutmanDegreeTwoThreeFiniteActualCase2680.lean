/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2680 : Family 10 := level10.get ⟨766,by decide⟩
def sourceMap2680 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2680 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2680_checked : acceptsGraphIso
    (source (graph core2680) (root 10) 0 4) DegreeTwoThreeSpectrum6684.graph sourceMap2680=true := by decide +kernel
theorem fusedMap2680_checked : acceptsGraphIso
    (fused (graph core2680) (root 10) 0 4) DegreeTwoThreeSpectrum5543.graph fusedMap2680=true := by decide +kernel
theorem certified2680 : Certified (graph core2680) (root 10) 0 4 :=
  of_native_maps core2680 DegreeTwoThreeSpectrum6684.graph DegreeTwoThreeSpectrum5543.graph
    sourceMap2680 fusedMap2680 sourceMap2680_checked fusedMap2680_checked
    DegreeTwoThreeFiniteComparisons.comparison2680
#print axioms sourceMap2680_checked
#print axioms fusedMap2680_checked
#print axioms certified2680
def sourceMap2680swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2680swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2680swap_checked : acceptsGraphIso
    (source (graph core2680) (root 10) 4 0) DegreeTwoThreeSpectrum6684.graph sourceMap2680swap=true := by decide +kernel
theorem fusedMap2680swap_checked : acceptsGraphIso
    (fused (graph core2680) (root 10) 4 0) DegreeTwoThreeSpectrum5543.graph fusedMap2680swap=true := by decide +kernel
theorem certified2680swap : Certified (graph core2680) (root 10) 4 0 :=
  of_native_maps core2680 DegreeTwoThreeSpectrum6684.graph DegreeTwoThreeSpectrum5543.graph
    sourceMap2680swap fusedMap2680swap sourceMap2680swap_checked fusedMap2680swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2680
#print axioms sourceMap2680swap_checked
#print axioms fusedMap2680swap_checked
#print axioms certified2680swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
