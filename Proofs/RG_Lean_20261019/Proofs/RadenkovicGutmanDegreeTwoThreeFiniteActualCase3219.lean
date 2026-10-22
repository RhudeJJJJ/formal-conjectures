/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3219 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap3219 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3219 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3219_checked : acceptsGraphIso
    (source (graph core3219) (root 8) 0 5) DegreeTwoThreeSpectrum4340.graph sourceMap3219=true := by decide +kernel
theorem fusedMap3219_checked : acceptsGraphIso
    (fused (graph core3219) (root 8) 0 5) DegreeTwoThreeSpectrum4341.graph fusedMap3219=true := by decide +kernel
theorem certified3219 : Certified (graph core3219) (root 8) 0 5 :=
  of_native_maps core3219 DegreeTwoThreeSpectrum4340.graph DegreeTwoThreeSpectrum4341.graph
    sourceMap3219 fusedMap3219 sourceMap3219_checked fusedMap3219_checked
    DegreeTwoThreeFiniteComparisons.comparison3219
#print axioms sourceMap3219_checked
#print axioms fusedMap3219_checked
#print axioms certified3219
def sourceMap3219swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3219swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3219swap_checked : acceptsGraphIso
    (source (graph core3219) (root 8) 5 0) DegreeTwoThreeSpectrum4340.graph sourceMap3219swap=true := by decide +kernel
theorem fusedMap3219swap_checked : acceptsGraphIso
    (fused (graph core3219) (root 8) 5 0) DegreeTwoThreeSpectrum4341.graph fusedMap3219swap=true := by decide +kernel
theorem certified3219swap : Certified (graph core3219) (root 8) 5 0 :=
  of_native_maps core3219 DegreeTwoThreeSpectrum4340.graph DegreeTwoThreeSpectrum4341.graph
    sourceMap3219swap fusedMap3219swap sourceMap3219swap_checked fusedMap3219swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3219
#print axioms sourceMap3219swap_checked
#print axioms fusedMap3219swap_checked
#print axioms certified3219swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
