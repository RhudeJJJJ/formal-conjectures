/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5219 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5219 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,5,6,7,8,2,3,4,0,9,10,11,12,13] (sourceLabel 4 2 5 v)
def fusedMap5219 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 2 5 v)
theorem sourceMap5219_checked : acceptsGraphIso
    (source (graph core5219) (root 4) 2 5) DegreeTwoThreeSpectrum1866.graph sourceMap5219=true := by decide +kernel
theorem fusedMap5219_checked : acceptsGraphIso
    (fused (graph core5219) (root 4) 2 5) DegreeTwoThreeSpectrum1716.graph fusedMap5219=true := by decide +kernel
theorem certified5219 : Certified (graph core5219) (root 4) 2 5 :=
  of_native_maps core5219 DegreeTwoThreeSpectrum1866.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap5219 fusedMap5219 sourceMap5219_checked fusedMap5219_checked
    DegreeTwoThreeFiniteComparisons.comparison5219
#print axioms sourceMap5219_checked
#print axioms fusedMap5219_checked
#print axioms certified5219
def sourceMap5219swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,5,6,7,8,0,9,10,11,12,13,2,3,4] (sourceLabel 4 5 2 v)
def fusedMap5219swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 5 2 v)
theorem sourceMap5219swap_checked : acceptsGraphIso
    (source (graph core5219) (root 4) 5 2) DegreeTwoThreeSpectrum1866.graph sourceMap5219swap=true := by decide +kernel
theorem fusedMap5219swap_checked : acceptsGraphIso
    (fused (graph core5219) (root 4) 5 2) DegreeTwoThreeSpectrum1716.graph fusedMap5219swap=true := by decide +kernel
theorem certified5219swap : Certified (graph core5219) (root 4) 5 2 :=
  of_native_maps core5219 DegreeTwoThreeSpectrum1866.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap5219swap fusedMap5219swap sourceMap5219swap_checked fusedMap5219swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5219
#print axioms sourceMap5219swap_checked
#print axioms fusedMap5219swap_checked
#print axioms certified5219swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
