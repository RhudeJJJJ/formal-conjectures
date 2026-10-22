/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2514 : Family 10 := level10.get ⟨263,by decide⟩
def sourceMap2514 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2514 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2514_checked : acceptsGraphIso
    (source (graph core2514) (root 10) 0 4) DegreeTwoThreeSpectrum5377.graph sourceMap2514=true := by decide +kernel
theorem fusedMap2514_checked : acceptsGraphIso
    (fused (graph core2514) (root 10) 0 4) DegreeTwoThreeSpectrum5378.graph fusedMap2514=true := by decide +kernel
theorem certified2514 : Certified (graph core2514) (root 10) 0 4 :=
  of_native_maps core2514 DegreeTwoThreeSpectrum5377.graph DegreeTwoThreeSpectrum5378.graph
    sourceMap2514 fusedMap2514 sourceMap2514_checked fusedMap2514_checked
    DegreeTwoThreeFiniteComparisons.comparison2514
#print axioms sourceMap2514_checked
#print axioms fusedMap2514_checked
#print axioms certified2514
def sourceMap2514swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2514swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2514swap_checked : acceptsGraphIso
    (source (graph core2514) (root 10) 4 0) DegreeTwoThreeSpectrum5377.graph sourceMap2514swap=true := by decide +kernel
theorem fusedMap2514swap_checked : acceptsGraphIso
    (fused (graph core2514) (root 10) 4 0) DegreeTwoThreeSpectrum5378.graph fusedMap2514swap=true := by decide +kernel
theorem certified2514swap : Certified (graph core2514) (root 10) 4 0 :=
  of_native_maps core2514 DegreeTwoThreeSpectrum5377.graph DegreeTwoThreeSpectrum5378.graph
    sourceMap2514swap fusedMap2514swap sourceMap2514swap_checked fusedMap2514swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2514
#print axioms sourceMap2514swap_checked
#print axioms fusedMap2514swap_checked
#print axioms certified2514swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
