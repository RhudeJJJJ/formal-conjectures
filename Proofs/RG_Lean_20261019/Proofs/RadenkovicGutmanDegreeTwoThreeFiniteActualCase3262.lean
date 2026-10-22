/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3262 : Family 9 := level9.get ⟨119,by decide⟩
def sourceMap3262 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3262 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3262_checked : acceptsGraphIso
    (source (graph core3262) (root 9) 0 5) DegreeTwoThreeSpectrum5884.graph sourceMap3262=true := by decide +kernel
theorem fusedMap3262_checked : acceptsGraphIso
    (fused (graph core3262) (root 9) 0 5) DegreeTwoThreeSpectrum5089.graph fusedMap3262=true := by decide +kernel
theorem certified3262 : Certified (graph core3262) (root 9) 0 5 :=
  of_native_maps core3262 DegreeTwoThreeSpectrum5884.graph DegreeTwoThreeSpectrum5089.graph
    sourceMap3262 fusedMap3262 sourceMap3262_checked fusedMap3262_checked
    DegreeTwoThreeFiniteComparisons.comparison3262
#print axioms sourceMap3262_checked
#print axioms fusedMap3262_checked
#print axioms certified3262
def sourceMap3262swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3262swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3262swap_checked : acceptsGraphIso
    (source (graph core3262) (root 9) 5 0) DegreeTwoThreeSpectrum5884.graph sourceMap3262swap=true := by decide +kernel
theorem fusedMap3262swap_checked : acceptsGraphIso
    (fused (graph core3262) (root 9) 5 0) DegreeTwoThreeSpectrum5089.graph fusedMap3262swap=true := by decide +kernel
theorem certified3262swap : Certified (graph core3262) (root 9) 5 0 :=
  of_native_maps core3262 DegreeTwoThreeSpectrum5884.graph DegreeTwoThreeSpectrum5089.graph
    sourceMap3262swap fusedMap3262swap sourceMap3262swap_checked fusedMap3262swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3262
#print axioms sourceMap3262swap_checked
#print axioms fusedMap3262swap_checked
#print axioms certified3262swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
