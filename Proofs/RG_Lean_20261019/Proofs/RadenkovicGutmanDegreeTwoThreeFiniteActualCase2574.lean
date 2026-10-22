/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2574 : Family 10 := level10.get ⟨458,by decide⟩
def sourceMap2574 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2574 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2574_checked : acceptsGraphIso
    (source (graph core2574) (root 10) 0 4) DegreeTwoThreeSpectrum5894.graph sourceMap2574=true := by decide +kernel
theorem fusedMap2574_checked : acceptsGraphIso
    (fused (graph core2574) (root 10) 0 4) DegreeTwoThreeSpectrum5895.graph fusedMap2574=true := by decide +kernel
theorem certified2574 : Certified (graph core2574) (root 10) 0 4 :=
  of_native_maps core2574 DegreeTwoThreeSpectrum5894.graph DegreeTwoThreeSpectrum5895.graph
    sourceMap2574 fusedMap2574 sourceMap2574_checked fusedMap2574_checked
    DegreeTwoThreeFiniteComparisons.comparison2574
#print axioms sourceMap2574_checked
#print axioms fusedMap2574_checked
#print axioms certified2574
def sourceMap2574swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2574swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2574swap_checked : acceptsGraphIso
    (source (graph core2574) (root 10) 4 0) DegreeTwoThreeSpectrum5894.graph sourceMap2574swap=true := by decide +kernel
theorem fusedMap2574swap_checked : acceptsGraphIso
    (fused (graph core2574) (root 10) 4 0) DegreeTwoThreeSpectrum5895.graph fusedMap2574swap=true := by decide +kernel
theorem certified2574swap : Certified (graph core2574) (root 10) 4 0 :=
  of_native_maps core2574 DegreeTwoThreeSpectrum5894.graph DegreeTwoThreeSpectrum5895.graph
    sourceMap2574swap fusedMap2574swap sourceMap2574swap_checked fusedMap2574swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2574
#print axioms sourceMap2574swap_checked
#print axioms fusedMap2574swap_checked
#print axioms certified2574swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
