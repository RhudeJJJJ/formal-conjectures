/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2868 : Family 10 := level10.get ⟨1243,by decide⟩
def sourceMap2868 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2868 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2868_checked : acceptsGraphIso
    (source (graph core2868) (root 10) 0 4) DegreeTwoThreeSpectrum6473.graph sourceMap2868=true := by decide +kernel
theorem fusedMap2868_checked : acceptsGraphIso
    (fused (graph core2868) (root 10) 0 4) DegreeTwoThreeSpectrum6474.graph fusedMap2868=true := by decide +kernel
theorem certified2868 : Certified (graph core2868) (root 10) 0 4 :=
  of_native_maps core2868 DegreeTwoThreeSpectrum6473.graph DegreeTwoThreeSpectrum6474.graph
    sourceMap2868 fusedMap2868 sourceMap2868_checked fusedMap2868_checked
    DegreeTwoThreeFiniteComparisons.comparison2868
#print axioms sourceMap2868_checked
#print axioms fusedMap2868_checked
#print axioms certified2868
def sourceMap2868swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2868swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2868swap_checked : acceptsGraphIso
    (source (graph core2868) (root 10) 4 0) DegreeTwoThreeSpectrum6473.graph sourceMap2868swap=true := by decide +kernel
theorem fusedMap2868swap_checked : acceptsGraphIso
    (fused (graph core2868) (root 10) 4 0) DegreeTwoThreeSpectrum6474.graph fusedMap2868swap=true := by decide +kernel
theorem certified2868swap : Certified (graph core2868) (root 10) 4 0 :=
  of_native_maps core2868 DegreeTwoThreeSpectrum6473.graph DegreeTwoThreeSpectrum6474.graph
    sourceMap2868swap fusedMap2868swap sourceMap2868swap_checked fusedMap2868swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2868
#print axioms sourceMap2868swap_checked
#print axioms fusedMap2868swap_checked
#print axioms certified2868swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
