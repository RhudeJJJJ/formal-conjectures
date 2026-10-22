/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3633 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap3633 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3633 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3633_checked : acceptsGraphIso
    (source (graph core3633) (root 8) 0 6) DegreeTwoThreeSpectrum5994.graph sourceMap3633=true := by decide +kernel
theorem fusedMap3633_checked : acceptsGraphIso
    (fused (graph core3633) (root 8) 0 6) DegreeTwoThreeSpectrum5996.graph fusedMap3633=true := by decide +kernel
theorem certified3633 : Certified (graph core3633) (root 8) 0 6 :=
  of_native_maps core3633 DegreeTwoThreeSpectrum5994.graph DegreeTwoThreeSpectrum5996.graph
    sourceMap3633 fusedMap3633 sourceMap3633_checked fusedMap3633_checked
    DegreeTwoThreeFiniteComparisons.comparison3633
#print axioms sourceMap3633_checked
#print axioms fusedMap3633_checked
#print axioms certified3633
def sourceMap3633swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3633swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3633swap_checked : acceptsGraphIso
    (source (graph core3633) (root 8) 6 0) DegreeTwoThreeSpectrum5994.graph sourceMap3633swap=true := by decide +kernel
theorem fusedMap3633swap_checked : acceptsGraphIso
    (fused (graph core3633) (root 8) 6 0) DegreeTwoThreeSpectrum5996.graph fusedMap3633swap=true := by decide +kernel
theorem certified3633swap : Certified (graph core3633) (root 8) 6 0 :=
  of_native_maps core3633 DegreeTwoThreeSpectrum5994.graph DegreeTwoThreeSpectrum5996.graph
    sourceMap3633swap fusedMap3633swap sourceMap3633swap_checked fusedMap3633swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3633
#print axioms sourceMap3633swap_checked
#print axioms fusedMap3633swap_checked
#print axioms certified3633swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
