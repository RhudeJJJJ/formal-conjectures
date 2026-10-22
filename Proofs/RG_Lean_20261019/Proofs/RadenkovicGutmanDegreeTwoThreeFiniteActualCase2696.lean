/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2696 : Family 10 := level10.get ⟨811,by decide⟩
def sourceMap2696 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2696 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2696_checked : acceptsGraphIso
    (source (graph core2696) (root 10) 0 4) DegreeTwoThreeSpectrum6772.graph sourceMap2696=true := by decide +kernel
theorem fusedMap2696_checked : acceptsGraphIso
    (fused (graph core2696) (root 10) 0 4) DegreeTwoThreeSpectrum5608.graph fusedMap2696=true := by decide +kernel
theorem certified2696 : Certified (graph core2696) (root 10) 0 4 :=
  of_native_maps core2696 DegreeTwoThreeSpectrum6772.graph DegreeTwoThreeSpectrum5608.graph
    sourceMap2696 fusedMap2696 sourceMap2696_checked fusedMap2696_checked
    DegreeTwoThreeFiniteComparisons.comparison2696
#print axioms sourceMap2696_checked
#print axioms fusedMap2696_checked
#print axioms certified2696
def sourceMap2696swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2696swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2696swap_checked : acceptsGraphIso
    (source (graph core2696) (root 10) 4 0) DegreeTwoThreeSpectrum6772.graph sourceMap2696swap=true := by decide +kernel
theorem fusedMap2696swap_checked : acceptsGraphIso
    (fused (graph core2696) (root 10) 4 0) DegreeTwoThreeSpectrum5608.graph fusedMap2696swap=true := by decide +kernel
theorem certified2696swap : Certified (graph core2696) (root 10) 4 0 :=
  of_native_maps core2696 DegreeTwoThreeSpectrum6772.graph DegreeTwoThreeSpectrum5608.graph
    sourceMap2696swap fusedMap2696swap sourceMap2696swap_checked fusedMap2696swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2696
#print axioms sourceMap2696swap_checked
#print axioms fusedMap2696swap_checked
#print axioms certified2696swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
