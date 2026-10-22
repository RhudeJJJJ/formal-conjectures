/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2755 : Family 10 := level10.get ⟨960,by decide⟩
def sourceMap2755 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2755 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2755_checked : acceptsGraphIso
    (source (graph core2755) (root 10) 0 4) DegreeTwoThreeSpectrum7033.graph sourceMap2755=true := by decide +kernel
theorem fusedMap2755_checked : acceptsGraphIso
    (fused (graph core2755) (root 10) 0 4) DegreeTwoThreeSpectrum5869.graph fusedMap2755=true := by decide +kernel
theorem certified2755 : Certified (graph core2755) (root 10) 0 4 :=
  of_native_maps core2755 DegreeTwoThreeSpectrum7033.graph DegreeTwoThreeSpectrum5869.graph
    sourceMap2755 fusedMap2755 sourceMap2755_checked fusedMap2755_checked
    DegreeTwoThreeFiniteComparisons.comparison2755
#print axioms sourceMap2755_checked
#print axioms fusedMap2755_checked
#print axioms certified2755
def sourceMap2755swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2755swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2755swap_checked : acceptsGraphIso
    (source (graph core2755) (root 10) 4 0) DegreeTwoThreeSpectrum7033.graph sourceMap2755swap=true := by decide +kernel
theorem fusedMap2755swap_checked : acceptsGraphIso
    (fused (graph core2755) (root 10) 4 0) DegreeTwoThreeSpectrum5869.graph fusedMap2755swap=true := by decide +kernel
theorem certified2755swap : Certified (graph core2755) (root 10) 4 0 :=
  of_native_maps core2755 DegreeTwoThreeSpectrum7033.graph DegreeTwoThreeSpectrum5869.graph
    sourceMap2755swap fusedMap2755swap sourceMap2755swap_checked fusedMap2755swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2755
#print axioms sourceMap2755swap_checked
#print axioms fusedMap2755swap_checked
#print axioms certified2755swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
