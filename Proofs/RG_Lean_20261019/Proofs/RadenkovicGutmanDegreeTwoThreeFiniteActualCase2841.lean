/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2841 : Family 10 := level10.get ⟨1180,by decide⟩
def sourceMap2841 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2841 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2841_checked : acceptsGraphIso
    (source (graph core2841) (root 10) 0 4) DegreeTwoThreeSpectrum6345.graph sourceMap2841=true := by decide +kernel
theorem fusedMap2841_checked : acceptsGraphIso
    (fused (graph core2841) (root 10) 0 4) DegreeTwoThreeSpectrum6346.graph fusedMap2841=true := by decide +kernel
theorem certified2841 : Certified (graph core2841) (root 10) 0 4 :=
  of_native_maps core2841 DegreeTwoThreeSpectrum6345.graph DegreeTwoThreeSpectrum6346.graph
    sourceMap2841 fusedMap2841 sourceMap2841_checked fusedMap2841_checked
    DegreeTwoThreeFiniteComparisons.comparison2841
#print axioms sourceMap2841_checked
#print axioms fusedMap2841_checked
#print axioms certified2841
def sourceMap2841swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2841swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2841swap_checked : acceptsGraphIso
    (source (graph core2841) (root 10) 4 0) DegreeTwoThreeSpectrum6345.graph sourceMap2841swap=true := by decide +kernel
theorem fusedMap2841swap_checked : acceptsGraphIso
    (fused (graph core2841) (root 10) 4 0) DegreeTwoThreeSpectrum6346.graph fusedMap2841swap=true := by decide +kernel
theorem certified2841swap : Certified (graph core2841) (root 10) 4 0 :=
  of_native_maps core2841 DegreeTwoThreeSpectrum6345.graph DegreeTwoThreeSpectrum6346.graph
    sourceMap2841swap fusedMap2841swap sourceMap2841swap_checked fusedMap2841swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2841
#print axioms sourceMap2841swap_checked
#print axioms fusedMap2841swap_checked
#print axioms certified2841swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
