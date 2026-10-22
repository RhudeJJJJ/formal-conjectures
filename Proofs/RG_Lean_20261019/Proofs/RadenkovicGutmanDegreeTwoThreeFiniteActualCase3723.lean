/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3723 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap3723 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3723 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3723_checked : acceptsGraphIso
    (source (graph core3723) (root 6) 0 8) DegreeTwoThreeSpectrum5140.graph sourceMap3723=true := by decide +kernel
theorem fusedMap3723_checked : acceptsGraphIso
    (fused (graph core3723) (root 6) 0 8) DegreeTwoThreeSpectrum5144.graph fusedMap3723=true := by decide +kernel
theorem certified3723 : Certified (graph core3723) (root 6) 0 8 :=
  of_native_maps core3723 DegreeTwoThreeSpectrum5140.graph DegreeTwoThreeSpectrum5144.graph
    sourceMap3723 fusedMap3723 sourceMap3723_checked fusedMap3723_checked
    DegreeTwoThreeFiniteComparisons.comparison3723
#print axioms sourceMap3723_checked
#print axioms fusedMap3723_checked
#print axioms certified3723
def sourceMap3723swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3723swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3723swap_checked : acceptsGraphIso
    (source (graph core3723) (root 6) 8 0) DegreeTwoThreeSpectrum5140.graph sourceMap3723swap=true := by decide +kernel
theorem fusedMap3723swap_checked : acceptsGraphIso
    (fused (graph core3723) (root 6) 8 0) DegreeTwoThreeSpectrum5144.graph fusedMap3723swap=true := by decide +kernel
theorem certified3723swap : Certified (graph core3723) (root 6) 8 0 :=
  of_native_maps core3723 DegreeTwoThreeSpectrum5140.graph DegreeTwoThreeSpectrum5144.graph
    sourceMap3723swap fusedMap3723swap sourceMap3723swap_checked fusedMap3723swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3723
#print axioms sourceMap3723swap_checked
#print axioms fusedMap3723swap_checked
#print axioms certified3723swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
