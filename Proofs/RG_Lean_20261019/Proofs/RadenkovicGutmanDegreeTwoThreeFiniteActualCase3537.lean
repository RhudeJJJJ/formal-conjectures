/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3537 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap3537 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3537 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3537_checked : acceptsGraphIso
    (source (graph core3537) (root 7) 0 6) DegreeTwoThreeSpectrum4183.graph sourceMap3537=true := by decide +kernel
theorem fusedMap3537_checked : acceptsGraphIso
    (fused (graph core3537) (root 7) 0 6) DegreeTwoThreeSpectrum4185.graph fusedMap3537=true := by decide +kernel
theorem certified3537 : Certified (graph core3537) (root 7) 0 6 :=
  of_native_maps core3537 DegreeTwoThreeSpectrum4183.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap3537 fusedMap3537 sourceMap3537_checked fusedMap3537_checked
    DegreeTwoThreeFiniteComparisons.comparison3537
#print axioms sourceMap3537_checked
#print axioms fusedMap3537_checked
#print axioms certified3537
def sourceMap3537swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3537swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3537swap_checked : acceptsGraphIso
    (source (graph core3537) (root 7) 6 0) DegreeTwoThreeSpectrum4183.graph sourceMap3537swap=true := by decide +kernel
theorem fusedMap3537swap_checked : acceptsGraphIso
    (fused (graph core3537) (root 7) 6 0) DegreeTwoThreeSpectrum4185.graph fusedMap3537swap=true := by decide +kernel
theorem certified3537swap : Certified (graph core3537) (root 7) 6 0 :=
  of_native_maps core3537 DegreeTwoThreeSpectrum4183.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap3537swap fusedMap3537swap sourceMap3537swap_checked fusedMap3537swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3537
#print axioms sourceMap3537swap_checked
#print axioms fusedMap3537swap_checked
#print axioms certified3537swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
