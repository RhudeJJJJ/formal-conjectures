/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2450 : Family 9 := level9.get ⟨690,by decide⟩
def sourceMap2450 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2450 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2450_checked : acceptsGraphIso
    (source (graph core2450) (root 9) 0 4) DegreeTwoThreeSpectrum4664.graph sourceMap2450=true := by decide +kernel
theorem fusedMap2450_checked : acceptsGraphIso
    (fused (graph core2450) (root 9) 0 4) DegreeTwoThreeSpectrum4665.graph fusedMap2450=true := by decide +kernel
theorem certified2450 : Certified (graph core2450) (root 9) 0 4 :=
  of_native_maps core2450 DegreeTwoThreeSpectrum4664.graph DegreeTwoThreeSpectrum4665.graph
    sourceMap2450 fusedMap2450 sourceMap2450_checked fusedMap2450_checked
    DegreeTwoThreeFiniteComparisons.comparison2450
#print axioms sourceMap2450_checked
#print axioms fusedMap2450_checked
#print axioms certified2450
def sourceMap2450swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2450swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2450swap_checked : acceptsGraphIso
    (source (graph core2450) (root 9) 4 0) DegreeTwoThreeSpectrum4664.graph sourceMap2450swap=true := by decide +kernel
theorem fusedMap2450swap_checked : acceptsGraphIso
    (fused (graph core2450) (root 9) 4 0) DegreeTwoThreeSpectrum4665.graph fusedMap2450swap=true := by decide +kernel
theorem certified2450swap : Certified (graph core2450) (root 9) 4 0 :=
  of_native_maps core2450 DegreeTwoThreeSpectrum4664.graph DegreeTwoThreeSpectrum4665.graph
    sourceMap2450swap fusedMap2450swap sourceMap2450swap_checked fusedMap2450swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2450
#print axioms sourceMap2450swap_checked
#print axioms fusedMap2450swap_checked
#print axioms certified2450swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
