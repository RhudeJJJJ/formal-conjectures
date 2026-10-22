/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3589 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap3589 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3589 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3589_checked : acceptsGraphIso
    (source (graph core3589) (root 8) 0 6) DegreeTwoThreeSpectrum5663.graph sourceMap3589=true := by decide +kernel
theorem fusedMap3589_checked : acceptsGraphIso
    (fused (graph core3589) (root 8) 0 6) DegreeTwoThreeSpectrum5665.graph fusedMap3589=true := by decide +kernel
theorem certified3589 : Certified (graph core3589) (root 8) 0 6 :=
  of_native_maps core3589 DegreeTwoThreeSpectrum5663.graph DegreeTwoThreeSpectrum5665.graph
    sourceMap3589 fusedMap3589 sourceMap3589_checked fusedMap3589_checked
    DegreeTwoThreeFiniteComparisons.comparison3589
#print axioms sourceMap3589_checked
#print axioms fusedMap3589_checked
#print axioms certified3589
def sourceMap3589swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3589swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3589swap_checked : acceptsGraphIso
    (source (graph core3589) (root 8) 6 0) DegreeTwoThreeSpectrum5663.graph sourceMap3589swap=true := by decide +kernel
theorem fusedMap3589swap_checked : acceptsGraphIso
    (fused (graph core3589) (root 8) 6 0) DegreeTwoThreeSpectrum5665.graph fusedMap3589swap=true := by decide +kernel
theorem certified3589swap : Certified (graph core3589) (root 8) 6 0 :=
  of_native_maps core3589 DegreeTwoThreeSpectrum5663.graph DegreeTwoThreeSpectrum5665.graph
    sourceMap3589swap fusedMap3589swap sourceMap3589swap_checked fusedMap3589swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3589
#print axioms sourceMap3589swap_checked
#print axioms fusedMap3589swap_checked
#print axioms certified3589swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
