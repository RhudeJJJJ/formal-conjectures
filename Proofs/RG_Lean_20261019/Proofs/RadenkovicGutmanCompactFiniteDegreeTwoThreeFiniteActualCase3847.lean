/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3847 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap3847 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 8 1 4 v)
def fusedMap3847 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3847_checked : acceptsGraphIso
    (source (graph core3847) (root 8) 1 4) DegreeTwoThreeSpectrum4625.graph sourceMap3847=true := by decide +kernel
theorem fusedMap3847_checked : acceptsGraphIso
    (fused (graph core3847) (root 8) 1 4) DegreeTwoThreeSpectrum4107.graph fusedMap3847=true := by decide +kernel
theorem certified3847 : Certified (graph core3847) (root 8) 1 4 :=
  of_native_maps core3847 DegreeTwoThreeSpectrum4625.graph DegreeTwoThreeSpectrum4107.graph
    sourceMap3847 fusedMap3847 sourceMap3847_checked fusedMap3847_checked
    DegreeTwoThreeFiniteComparisons.comparison3847
#print axioms sourceMap3847_checked
#print axioms fusedMap3847_checked
#print axioms certified3847
def sourceMap3847swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14,15] (sourceLabel 8 4 1 v)
def fusedMap3847swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3847swap_checked : acceptsGraphIso
    (source (graph core3847) (root 8) 4 1) DegreeTwoThreeSpectrum4625.graph sourceMap3847swap=true := by decide +kernel
theorem fusedMap3847swap_checked : acceptsGraphIso
    (fused (graph core3847) (root 8) 4 1) DegreeTwoThreeSpectrum4107.graph fusedMap3847swap=true := by decide +kernel
theorem certified3847swap : Certified (graph core3847) (root 8) 4 1 :=
  of_native_maps core3847 DegreeTwoThreeSpectrum4625.graph DegreeTwoThreeSpectrum4107.graph
    sourceMap3847swap fusedMap3847swap sourceMap3847swap_checked fusedMap3847swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3847
#print axioms sourceMap3847swap_checked
#print axioms fusedMap3847swap_checked
#print axioms certified3847swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
