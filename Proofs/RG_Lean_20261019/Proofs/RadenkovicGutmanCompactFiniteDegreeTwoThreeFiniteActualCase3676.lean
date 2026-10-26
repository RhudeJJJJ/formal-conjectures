/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3676 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap3676 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3676 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3676_checked : acceptsGraphIso
    (source (graph core3676) (root 7) 0 7) DegreeTwoThreeSpectrum5709.graph sourceMap3676=true := by decide +kernel
theorem fusedMap3676_checked : acceptsGraphIso
    (fused (graph core3676) (root 7) 0 7) DegreeTwoThreeSpectrum5051.graph fusedMap3676=true := by decide +kernel
theorem certified3676 : Certified (graph core3676) (root 7) 0 7 :=
  of_native_maps core3676 DegreeTwoThreeSpectrum5709.graph DegreeTwoThreeSpectrum5051.graph
    sourceMap3676 fusedMap3676 sourceMap3676_checked fusedMap3676_checked
    DegreeTwoThreeFiniteComparisons.comparison3676
#print axioms sourceMap3676_checked
#print axioms fusedMap3676_checked
#print axioms certified3676
def sourceMap3676swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3676swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3676swap_checked : acceptsGraphIso
    (source (graph core3676) (root 7) 7 0) DegreeTwoThreeSpectrum5709.graph sourceMap3676swap=true := by decide +kernel
theorem fusedMap3676swap_checked : acceptsGraphIso
    (fused (graph core3676) (root 7) 7 0) DegreeTwoThreeSpectrum5051.graph fusedMap3676swap=true := by decide +kernel
theorem certified3676swap : Certified (graph core3676) (root 7) 7 0 :=
  of_native_maps core3676 DegreeTwoThreeSpectrum5709.graph DegreeTwoThreeSpectrum5051.graph
    sourceMap3676swap fusedMap3676swap sourceMap3676swap_checked fusedMap3676swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3676
#print axioms sourceMap3676swap_checked
#print axioms fusedMap3676swap_checked
#print axioms certified3676swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
