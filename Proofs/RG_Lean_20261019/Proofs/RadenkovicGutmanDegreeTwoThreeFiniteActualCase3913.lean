/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3913 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap3913 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3913 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3913_checked : acceptsGraphIso
    (source (graph core3913) (root 8) 1 4) DegreeTwoThreeSpectrum4819.graph sourceMap3913=true := by decide +kernel
theorem fusedMap3913_checked : acceptsGraphIso
    (fused (graph core3913) (root 8) 1 4) DegreeTwoThreeSpectrum4448.graph fusedMap3913=true := by decide +kernel
theorem certified3913 : Certified (graph core3913) (root 8) 1 4 :=
  of_native_maps core3913 DegreeTwoThreeSpectrum4819.graph DegreeTwoThreeSpectrum4448.graph
    sourceMap3913 fusedMap3913 sourceMap3913_checked fusedMap3913_checked
    DegreeTwoThreeFiniteComparisons.comparison3913
#print axioms sourceMap3913_checked
#print axioms fusedMap3913_checked
#print axioms certified3913
def sourceMap3913swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3913swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3913swap_checked : acceptsGraphIso
    (source (graph core3913) (root 8) 4 1) DegreeTwoThreeSpectrum4819.graph sourceMap3913swap=true := by decide +kernel
theorem fusedMap3913swap_checked : acceptsGraphIso
    (fused (graph core3913) (root 8) 4 1) DegreeTwoThreeSpectrum4448.graph fusedMap3913swap=true := by decide +kernel
theorem certified3913swap : Certified (graph core3913) (root 8) 4 1 :=
  of_native_maps core3913 DegreeTwoThreeSpectrum4819.graph DegreeTwoThreeSpectrum4448.graph
    sourceMap3913swap fusedMap3913swap sourceMap3913swap_checked fusedMap3913swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3913
#print axioms sourceMap3913swap_checked
#print axioms fusedMap3913swap_checked
#print axioms certified3913swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
