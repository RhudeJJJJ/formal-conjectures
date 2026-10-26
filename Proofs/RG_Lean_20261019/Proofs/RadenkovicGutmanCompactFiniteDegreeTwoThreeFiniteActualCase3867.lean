/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3867 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap3867 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3867 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3867_checked : acceptsGraphIso
    (source (graph core3867) (root 8) 1 4) DegreeTwoThreeSpectrum4426.graph sourceMap3867=true := by decide +kernel
theorem fusedMap3867_checked : acceptsGraphIso
    (fused (graph core3867) (root 8) 1 4) DegreeTwoThreeSpectrum3989.graph fusedMap3867=true := by decide +kernel
theorem certified3867 : Certified (graph core3867) (root 8) 1 4 :=
  of_native_maps core3867 DegreeTwoThreeSpectrum4426.graph DegreeTwoThreeSpectrum3989.graph
    sourceMap3867 fusedMap3867 sourceMap3867_checked fusedMap3867_checked
    DegreeTwoThreeFiniteComparisons.comparison3867
#print axioms sourceMap3867_checked
#print axioms fusedMap3867_checked
#print axioms certified3867
def sourceMap3867swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3867swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3867swap_checked : acceptsGraphIso
    (source (graph core3867) (root 8) 4 1) DegreeTwoThreeSpectrum4426.graph sourceMap3867swap=true := by decide +kernel
theorem fusedMap3867swap_checked : acceptsGraphIso
    (fused (graph core3867) (root 8) 4 1) DegreeTwoThreeSpectrum3989.graph fusedMap3867swap=true := by decide +kernel
theorem certified3867swap : Certified (graph core3867) (root 8) 4 1 :=
  of_native_maps core3867 DegreeTwoThreeSpectrum4426.graph DegreeTwoThreeSpectrum3989.graph
    sourceMap3867swap fusedMap3867swap sourceMap3867swap_checked fusedMap3867swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3867
#print axioms sourceMap3867swap_checked
#print axioms fusedMap3867swap_checked
#print axioms certified3867swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
