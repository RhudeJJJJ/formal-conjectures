/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3892 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap3892 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3892 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3892_checked : acceptsGraphIso
    (source (graph core3892) (root 8) 1 4) DegreeTwoThreeSpectrum4697.graph sourceMap3892=true := by decide +kernel
theorem fusedMap3892_checked : acceptsGraphIso
    (fused (graph core3892) (root 8) 1 4) DegreeTwoThreeSpectrum4213.graph fusedMap3892=true := by decide +kernel
theorem certified3892 : Certified (graph core3892) (root 8) 1 4 :=
  of_native_maps core3892 DegreeTwoThreeSpectrum4697.graph DegreeTwoThreeSpectrum4213.graph
    sourceMap3892 fusedMap3892 sourceMap3892_checked fusedMap3892_checked
    DegreeTwoThreeFiniteComparisons.comparison3892
#print axioms sourceMap3892_checked
#print axioms fusedMap3892_checked
#print axioms certified3892
def sourceMap3892swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3892swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3892swap_checked : acceptsGraphIso
    (source (graph core3892) (root 8) 4 1) DegreeTwoThreeSpectrum4697.graph sourceMap3892swap=true := by decide +kernel
theorem fusedMap3892swap_checked : acceptsGraphIso
    (fused (graph core3892) (root 8) 4 1) DegreeTwoThreeSpectrum4213.graph fusedMap3892swap=true := by decide +kernel
theorem certified3892swap : Certified (graph core3892) (root 8) 4 1 :=
  of_native_maps core3892 DegreeTwoThreeSpectrum4697.graph DegreeTwoThreeSpectrum4213.graph
    sourceMap3892swap fusedMap3892swap sourceMap3892swap_checked fusedMap3892swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3892
#print axioms sourceMap3892swap_checked
#print axioms fusedMap3892swap_checked
#print axioms certified3892swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
