/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3600 : Family 8 := level8.get ⟨183,by decide⟩
def sourceMap3600 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3600 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3600_checked : acceptsGraphIso
    (source (graph core3600) (root 8) 0 6) DegreeTwoThreeSpectrum5840.graph sourceMap3600=true := by decide +kernel
theorem fusedMap3600_checked : acceptsGraphIso
    (fused (graph core3600) (root 8) 0 6) DegreeTwoThreeSpectrum5842.graph fusedMap3600=true := by decide +kernel
theorem certified3600 : Certified (graph core3600) (root 8) 0 6 :=
  of_native_maps core3600 DegreeTwoThreeSpectrum5840.graph DegreeTwoThreeSpectrum5842.graph
    sourceMap3600 fusedMap3600 sourceMap3600_checked fusedMap3600_checked
    DegreeTwoThreeFiniteComparisons.comparison3600
#print axioms sourceMap3600_checked
#print axioms fusedMap3600_checked
#print axioms certified3600
def sourceMap3600swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3600swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3600swap_checked : acceptsGraphIso
    (source (graph core3600) (root 8) 6 0) DegreeTwoThreeSpectrum5840.graph sourceMap3600swap=true := by decide +kernel
theorem fusedMap3600swap_checked : acceptsGraphIso
    (fused (graph core3600) (root 8) 6 0) DegreeTwoThreeSpectrum5842.graph fusedMap3600swap=true := by decide +kernel
theorem certified3600swap : Certified (graph core3600) (root 8) 6 0 :=
  of_native_maps core3600 DegreeTwoThreeSpectrum5840.graph DegreeTwoThreeSpectrum5842.graph
    sourceMap3600swap fusedMap3600swap sourceMap3600swap_checked fusedMap3600swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3600
#print axioms sourceMap3600swap_checked
#print axioms fusedMap3600swap_checked
#print axioms certified3600swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
