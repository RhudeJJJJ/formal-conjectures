/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3227 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap3227 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3227 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3227_checked : acceptsGraphIso
    (source (graph core3227) (root 8) 0 5) DegreeTwoThreeSpectrum4457.graph sourceMap3227=true := by decide +kernel
theorem fusedMap3227_checked : acceptsGraphIso
    (fused (graph core3227) (root 8) 0 5) DegreeTwoThreeSpectrum4458.graph fusedMap3227=true := by decide +kernel
theorem certified3227 : Certified (graph core3227) (root 8) 0 5 :=
  of_native_maps core3227 DegreeTwoThreeSpectrum4457.graph DegreeTwoThreeSpectrum4458.graph
    sourceMap3227 fusedMap3227 sourceMap3227_checked fusedMap3227_checked
    DegreeTwoThreeFiniteComparisons.comparison3227
#print axioms sourceMap3227_checked
#print axioms fusedMap3227_checked
#print axioms certified3227
def sourceMap3227swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3227swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3227swap_checked : acceptsGraphIso
    (source (graph core3227) (root 8) 5 0) DegreeTwoThreeSpectrum4457.graph sourceMap3227swap=true := by decide +kernel
theorem fusedMap3227swap_checked : acceptsGraphIso
    (fused (graph core3227) (root 8) 5 0) DegreeTwoThreeSpectrum4458.graph fusedMap3227swap=true := by decide +kernel
theorem certified3227swap : Certified (graph core3227) (root 8) 5 0 :=
  of_native_maps core3227 DegreeTwoThreeSpectrum4457.graph DegreeTwoThreeSpectrum4458.graph
    sourceMap3227swap fusedMap3227swap sourceMap3227swap_checked fusedMap3227swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3227
#print axioms sourceMap3227swap_checked
#print axioms fusedMap3227swap_checked
#print axioms certified3227swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
