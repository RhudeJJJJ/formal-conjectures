/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2718 : Family 10 := level10.get ⟨869,by decide⟩
def sourceMap2718 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2718 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2718_checked : acceptsGraphIso
    (source (graph core2718) (root 10) 0 4) DegreeTwoThreeSpectrum6928.graph sourceMap2718=true := by decide +kernel
theorem fusedMap2718_checked : acceptsGraphIso
    (fused (graph core2718) (root 10) 0 4) DegreeTwoThreeSpectrum5710.graph fusedMap2718=true := by decide +kernel
theorem certified2718 : Certified (graph core2718) (root 10) 0 4 :=
  of_native_maps core2718 DegreeTwoThreeSpectrum6928.graph DegreeTwoThreeSpectrum5710.graph
    sourceMap2718 fusedMap2718 sourceMap2718_checked fusedMap2718_checked
    DegreeTwoThreeFiniteComparisons.comparison2718
#print axioms sourceMap2718_checked
#print axioms fusedMap2718_checked
#print axioms certified2718
def sourceMap2718swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2718swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2718swap_checked : acceptsGraphIso
    (source (graph core2718) (root 10) 4 0) DegreeTwoThreeSpectrum6928.graph sourceMap2718swap=true := by decide +kernel
theorem fusedMap2718swap_checked : acceptsGraphIso
    (fused (graph core2718) (root 10) 4 0) DegreeTwoThreeSpectrum5710.graph fusedMap2718swap=true := by decide +kernel
theorem certified2718swap : Certified (graph core2718) (root 10) 4 0 :=
  of_native_maps core2718 DegreeTwoThreeSpectrum6928.graph DegreeTwoThreeSpectrum5710.graph
    sourceMap2718swap fusedMap2718swap sourceMap2718swap_checked fusedMap2718swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2718
#print axioms sourceMap2718swap_checked
#print axioms fusedMap2718swap_checked
#print axioms certified2718swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
