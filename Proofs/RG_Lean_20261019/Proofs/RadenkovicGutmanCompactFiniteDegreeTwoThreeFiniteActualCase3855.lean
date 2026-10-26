/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3855 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap3855 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3855 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3855_checked : acceptsGraphIso
    (source (graph core3855) (root 8) 1 4) DegreeTwoThreeSpectrum4246.graph sourceMap3855=true := by decide +kernel
theorem fusedMap3855_checked : acceptsGraphIso
    (fused (graph core3855) (root 8) 1 4) DegreeTwoThreeSpectrum3905.graph fusedMap3855=true := by decide +kernel
theorem certified3855 : Certified (graph core3855) (root 8) 1 4 :=
  of_native_maps core3855 DegreeTwoThreeSpectrum4246.graph DegreeTwoThreeSpectrum3905.graph
    sourceMap3855 fusedMap3855 sourceMap3855_checked fusedMap3855_checked
    DegreeTwoThreeFiniteComparisons.comparison3855
#print axioms sourceMap3855_checked
#print axioms fusedMap3855_checked
#print axioms certified3855
def sourceMap3855swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3855swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3855swap_checked : acceptsGraphIso
    (source (graph core3855) (root 8) 4 1) DegreeTwoThreeSpectrum4246.graph sourceMap3855swap=true := by decide +kernel
theorem fusedMap3855swap_checked : acceptsGraphIso
    (fused (graph core3855) (root 8) 4 1) DegreeTwoThreeSpectrum3905.graph fusedMap3855swap=true := by decide +kernel
theorem certified3855swap : Certified (graph core3855) (root 8) 4 1 :=
  of_native_maps core3855 DegreeTwoThreeSpectrum4246.graph DegreeTwoThreeSpectrum3905.graph
    sourceMap3855swap fusedMap3855swap sourceMap3855swap_checked fusedMap3855swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3855
#print axioms sourceMap3855swap_checked
#print axioms fusedMap3855swap_checked
#print axioms certified3855swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
