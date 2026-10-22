/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1852 : Family 10 := level10.get ⟨1262,by decide⟩
def sourceMap1852 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1852 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1852_checked : acceptsGraphIso
    (source (graph core1852) (root 10) 0 2) DegreeTwoThreeSpectrum3407.graph sourceMap1852=true := by decide +kernel
theorem fusedMap1852_checked : acceptsGraphIso
    (fused (graph core1852) (root 10) 0 2) DegreeTwoThreeSpectrum3408.graph fusedMap1852=true := by decide +kernel
theorem certified1852 : Certified (graph core1852) (root 10) 0 2 :=
  of_native_maps core1852 DegreeTwoThreeSpectrum3407.graph DegreeTwoThreeSpectrum3408.graph
    sourceMap1852 fusedMap1852 sourceMap1852_checked fusedMap1852_checked
    DegreeTwoThreeFiniteComparisons.comparison1852
#print axioms sourceMap1852_checked
#print axioms fusedMap1852_checked
#print axioms certified1852
def sourceMap1852swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1852swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1852swap_checked : acceptsGraphIso
    (source (graph core1852) (root 10) 2 0) DegreeTwoThreeSpectrum3407.graph sourceMap1852swap=true := by decide +kernel
theorem fusedMap1852swap_checked : acceptsGraphIso
    (fused (graph core1852) (root 10) 2 0) DegreeTwoThreeSpectrum3408.graph fusedMap1852swap=true := by decide +kernel
theorem certified1852swap : Certified (graph core1852) (root 10) 2 0 :=
  of_native_maps core1852 DegreeTwoThreeSpectrum3407.graph DegreeTwoThreeSpectrum3408.graph
    sourceMap1852swap fusedMap1852swap sourceMap1852swap_checked fusedMap1852swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1852
#print axioms sourceMap1852swap_checked
#print axioms fusedMap1852swap_checked
#print axioms certified1852swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
