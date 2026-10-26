/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3574 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap3574 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3574 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3574_checked : acceptsGraphIso
    (source (graph core3574) (root 8) 0 6) DegreeTwoThreeSpectrum5331.graph sourceMap3574=true := by decide +kernel
theorem fusedMap3574_checked : acceptsGraphIso
    (fused (graph core3574) (root 8) 0 6) DegreeTwoThreeSpectrum5333.graph fusedMap3574=true := by decide +kernel
theorem certified3574 : Certified (graph core3574) (root 8) 0 6 :=
  of_native_maps core3574 DegreeTwoThreeSpectrum5331.graph DegreeTwoThreeSpectrum5333.graph
    sourceMap3574 fusedMap3574 sourceMap3574_checked fusedMap3574_checked
    DegreeTwoThreeFiniteComparisons.comparison3574
#print axioms sourceMap3574_checked
#print axioms fusedMap3574_checked
#print axioms certified3574
def sourceMap3574swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3574swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3574swap_checked : acceptsGraphIso
    (source (graph core3574) (root 8) 6 0) DegreeTwoThreeSpectrum5331.graph sourceMap3574swap=true := by decide +kernel
theorem fusedMap3574swap_checked : acceptsGraphIso
    (fused (graph core3574) (root 8) 6 0) DegreeTwoThreeSpectrum5333.graph fusedMap3574swap=true := by decide +kernel
theorem certified3574swap : Certified (graph core3574) (root 8) 6 0 :=
  of_native_maps core3574 DegreeTwoThreeSpectrum5331.graph DegreeTwoThreeSpectrum5333.graph
    sourceMap3574swap fusedMap3574swap sourceMap3574swap_checked fusedMap3574swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3574
#print axioms sourceMap3574swap_checked
#print axioms fusedMap3574swap_checked
#print axioms certified3574swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
