/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3833 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap3833 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,6,7,8,9,1,2,3,4,5] (sourceLabel 8 1 4 v)
def fusedMap3833 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3833_checked : acceptsGraphIso
    (source (graph core3833) (root 8) 1 4) DegreeTwoThreeSpectrum4158.graph sourceMap3833=true := by decide +kernel
theorem fusedMap3833_checked : acceptsGraphIso
    (fused (graph core3833) (root 8) 1 4) DegreeTwoThreeSpectrum3888.graph fusedMap3833=true := by decide +kernel
theorem certified3833 : Certified (graph core3833) (root 8) 1 4 :=
  of_native_maps core3833 DegreeTwoThreeSpectrum4158.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap3833 fusedMap3833 sourceMap3833_checked fusedMap3833_checked
    DegreeTwoThreeFiniteComparisons.comparison3833
#print axioms sourceMap3833_checked
#print axioms fusedMap3833_checked
#print axioms certified3833
def sourceMap3833swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,6,7,1,2,3,4,5,8,9] (sourceLabel 8 4 1 v)
def fusedMap3833swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3833swap_checked : acceptsGraphIso
    (source (graph core3833) (root 8) 4 1) DegreeTwoThreeSpectrum4158.graph sourceMap3833swap=true := by decide +kernel
theorem fusedMap3833swap_checked : acceptsGraphIso
    (fused (graph core3833) (root 8) 4 1) DegreeTwoThreeSpectrum3888.graph fusedMap3833swap=true := by decide +kernel
theorem certified3833swap : Certified (graph core3833) (root 8) 4 1 :=
  of_native_maps core3833 DegreeTwoThreeSpectrum4158.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap3833swap fusedMap3833swap sourceMap3833swap_checked fusedMap3833swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3833
#print axioms sourceMap3833swap_checked
#print axioms fusedMap3833swap_checked
#print axioms certified3833swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
