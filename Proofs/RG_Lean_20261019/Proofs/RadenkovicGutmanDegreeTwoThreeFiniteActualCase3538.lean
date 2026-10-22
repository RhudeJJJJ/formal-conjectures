/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3538 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap3538 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3538 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3538_checked : acceptsGraphIso
    (source (graph core3538) (root 7) 0 6) DegreeTwoThreeSpectrum4205.graph sourceMap3538=true := by decide +kernel
theorem fusedMap3538_checked : acceptsGraphIso
    (fused (graph core3538) (root 7) 0 6) DegreeTwoThreeSpectrum4207.graph fusedMap3538=true := by decide +kernel
theorem certified3538 : Certified (graph core3538) (root 7) 0 6 :=
  of_native_maps core3538 DegreeTwoThreeSpectrum4205.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap3538 fusedMap3538 sourceMap3538_checked fusedMap3538_checked
    DegreeTwoThreeFiniteComparisons.comparison3538
#print axioms sourceMap3538_checked
#print axioms fusedMap3538_checked
#print axioms certified3538
def sourceMap3538swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3538swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3538swap_checked : acceptsGraphIso
    (source (graph core3538) (root 7) 6 0) DegreeTwoThreeSpectrum4205.graph sourceMap3538swap=true := by decide +kernel
theorem fusedMap3538swap_checked : acceptsGraphIso
    (fused (graph core3538) (root 7) 6 0) DegreeTwoThreeSpectrum4207.graph fusedMap3538swap=true := by decide +kernel
theorem certified3538swap : Certified (graph core3538) (root 7) 6 0 :=
  of_native_maps core3538 DegreeTwoThreeSpectrum4205.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap3538swap fusedMap3538swap sourceMap3538swap_checked fusedMap3538swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3538
#print axioms sourceMap3538swap_checked
#print axioms fusedMap3538swap_checked
#print axioms certified3538swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
