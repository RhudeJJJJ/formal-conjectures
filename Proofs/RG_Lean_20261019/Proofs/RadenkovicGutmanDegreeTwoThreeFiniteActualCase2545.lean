/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2545 : Family 10 := level10.get ⟨363,by decide⟩
def sourceMap2545 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2545 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2545_checked : acceptsGraphIso
    (source (graph core2545) (root 10) 0 4) DegreeTwoThreeSpectrum5648.graph sourceMap2545=true := by decide +kernel
theorem fusedMap2545_checked : acceptsGraphIso
    (fused (graph core2545) (root 10) 0 4) DegreeTwoThreeSpectrum5652.graph fusedMap2545=true := by decide +kernel
theorem certified2545 : Certified (graph core2545) (root 10) 0 4 :=
  of_native_maps core2545 DegreeTwoThreeSpectrum5648.graph DegreeTwoThreeSpectrum5652.graph
    sourceMap2545 fusedMap2545 sourceMap2545_checked fusedMap2545_checked
    DegreeTwoThreeFiniteComparisons.comparison2545
#print axioms sourceMap2545_checked
#print axioms fusedMap2545_checked
#print axioms certified2545
def sourceMap2545swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2545swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2545swap_checked : acceptsGraphIso
    (source (graph core2545) (root 10) 4 0) DegreeTwoThreeSpectrum5648.graph sourceMap2545swap=true := by decide +kernel
theorem fusedMap2545swap_checked : acceptsGraphIso
    (fused (graph core2545) (root 10) 4 0) DegreeTwoThreeSpectrum5652.graph fusedMap2545swap=true := by decide +kernel
theorem certified2545swap : Certified (graph core2545) (root 10) 4 0 :=
  of_native_maps core2545 DegreeTwoThreeSpectrum5648.graph DegreeTwoThreeSpectrum5652.graph
    sourceMap2545swap fusedMap2545swap sourceMap2545swap_checked fusedMap2545swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2545
#print axioms sourceMap2545swap_checked
#print axioms fusedMap2545swap_checked
#print axioms certified2545swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
