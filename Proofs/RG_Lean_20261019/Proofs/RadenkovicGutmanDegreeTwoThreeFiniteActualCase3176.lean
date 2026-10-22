/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3176 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap3176 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3176 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3176_checked : acceptsGraphIso
    (source (graph core3176) (root 8) 0 5) DegreeTwoThreeSpectrum4364.graph sourceMap3176=true := by decide +kernel
theorem fusedMap3176_checked : acceptsGraphIso
    (fused (graph core3176) (root 8) 0 5) DegreeTwoThreeSpectrum3950.graph fusedMap3176=true := by decide +kernel
theorem certified3176 : Certified (graph core3176) (root 8) 0 5 :=
  of_native_maps core3176 DegreeTwoThreeSpectrum4364.graph DegreeTwoThreeSpectrum3950.graph
    sourceMap3176 fusedMap3176 sourceMap3176_checked fusedMap3176_checked
    DegreeTwoThreeFiniteComparisons.comparison3176
#print axioms sourceMap3176_checked
#print axioms fusedMap3176_checked
#print axioms certified3176
def sourceMap3176swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3176swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3176swap_checked : acceptsGraphIso
    (source (graph core3176) (root 8) 5 0) DegreeTwoThreeSpectrum4364.graph sourceMap3176swap=true := by decide +kernel
theorem fusedMap3176swap_checked : acceptsGraphIso
    (fused (graph core3176) (root 8) 5 0) DegreeTwoThreeSpectrum3950.graph fusedMap3176swap=true := by decide +kernel
theorem certified3176swap : Certified (graph core3176) (root 8) 5 0 :=
  of_native_maps core3176 DegreeTwoThreeSpectrum4364.graph DegreeTwoThreeSpectrum3950.graph
    sourceMap3176swap fusedMap3176swap sourceMap3176swap_checked fusedMap3176swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3176
#print axioms sourceMap3176swap_checked
#print axioms fusedMap3176swap_checked
#print axioms certified3176swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
