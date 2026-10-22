/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3151 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap3151 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3151 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3151_checked : acceptsGraphIso
    (source (graph core3151) (root 8) 0 5) DegreeTwoThreeSpectrum3973.graph sourceMap3151=true := by decide +kernel
theorem fusedMap3151_checked : acceptsGraphIso
    (fused (graph core3151) (root 8) 0 5) DegreeTwoThreeSpectrum3974.graph fusedMap3151=true := by decide +kernel
theorem certified3151 : Certified (graph core3151) (root 8) 0 5 :=
  of_native_maps core3151 DegreeTwoThreeSpectrum3973.graph DegreeTwoThreeSpectrum3974.graph
    sourceMap3151 fusedMap3151 sourceMap3151_checked fusedMap3151_checked
    DegreeTwoThreeFiniteComparisons.comparison3151
#print axioms sourceMap3151_checked
#print axioms fusedMap3151_checked
#print axioms certified3151
def sourceMap3151swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3151swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3151swap_checked : acceptsGraphIso
    (source (graph core3151) (root 8) 5 0) DegreeTwoThreeSpectrum3973.graph sourceMap3151swap=true := by decide +kernel
theorem fusedMap3151swap_checked : acceptsGraphIso
    (fused (graph core3151) (root 8) 5 0) DegreeTwoThreeSpectrum3974.graph fusedMap3151swap=true := by decide +kernel
theorem certified3151swap : Certified (graph core3151) (root 8) 5 0 :=
  of_native_maps core3151 DegreeTwoThreeSpectrum3973.graph DegreeTwoThreeSpectrum3974.graph
    sourceMap3151swap fusedMap3151swap sourceMap3151swap_checked fusedMap3151swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3151
#print axioms sourceMap3151swap_checked
#print axioms fusedMap3151swap_checked
#print axioms certified3151swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
