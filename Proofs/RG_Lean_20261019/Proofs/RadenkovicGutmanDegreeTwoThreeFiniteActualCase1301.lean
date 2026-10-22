/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1301 : Family 9 := level9.get ⟨360,by decide⟩
def sourceMap1301 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1301 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1301_checked : acceptsGraphIso
    (source (graph core1301) (root 9) 0 2) DegreeTwoThreeSpectrum1997.graph sourceMap1301=true := by decide +kernel
theorem fusedMap1301_checked : acceptsGraphIso
    (fused (graph core1301) (root 9) 0 2) DegreeTwoThreeSpectrum1998.graph fusedMap1301=true := by decide +kernel
theorem certified1301 : Certified (graph core1301) (root 9) 0 2 :=
  of_native_maps core1301 DegreeTwoThreeSpectrum1997.graph DegreeTwoThreeSpectrum1998.graph
    sourceMap1301 fusedMap1301 sourceMap1301_checked fusedMap1301_checked
    DegreeTwoThreeFiniteComparisons.comparison1301
#print axioms sourceMap1301_checked
#print axioms fusedMap1301_checked
#print axioms certified1301
def sourceMap1301swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1301swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1301swap_checked : acceptsGraphIso
    (source (graph core1301) (root 9) 2 0) DegreeTwoThreeSpectrum1997.graph sourceMap1301swap=true := by decide +kernel
theorem fusedMap1301swap_checked : acceptsGraphIso
    (fused (graph core1301) (root 9) 2 0) DegreeTwoThreeSpectrum1998.graph fusedMap1301swap=true := by decide +kernel
theorem certified1301swap : Certified (graph core1301) (root 9) 2 0 :=
  of_native_maps core1301 DegreeTwoThreeSpectrum1997.graph DegreeTwoThreeSpectrum1998.graph
    sourceMap1301swap fusedMap1301swap sourceMap1301swap_checked fusedMap1301swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1301
#print axioms sourceMap1301swap_checked
#print axioms fusedMap1301swap_checked
#print axioms certified1301swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
