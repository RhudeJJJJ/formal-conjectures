/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3323 : Family 9 := level9.get ⟨301,by decide⟩
def sourceMap3323 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3323 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3323_checked : acceptsGraphIso
    (source (graph core3323) (root 9) 0 5) DegreeTwoThreeSpectrum5870.graph sourceMap3323=true := by decide +kernel
theorem fusedMap3323_checked : acceptsGraphIso
    (fused (graph core3323) (root 9) 0 5) DegreeTwoThreeSpectrum5871.graph fusedMap3323=true := by decide +kernel
theorem certified3323 : Certified (graph core3323) (root 9) 0 5 :=
  of_native_maps core3323 DegreeTwoThreeSpectrum5870.graph DegreeTwoThreeSpectrum5871.graph
    sourceMap3323 fusedMap3323 sourceMap3323_checked fusedMap3323_checked
    DegreeTwoThreeFiniteComparisons.comparison3323
#print axioms sourceMap3323_checked
#print axioms fusedMap3323_checked
#print axioms certified3323
def sourceMap3323swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3323swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3323swap_checked : acceptsGraphIso
    (source (graph core3323) (root 9) 5 0) DegreeTwoThreeSpectrum5870.graph sourceMap3323swap=true := by decide +kernel
theorem fusedMap3323swap_checked : acceptsGraphIso
    (fused (graph core3323) (root 9) 5 0) DegreeTwoThreeSpectrum5871.graph fusedMap3323swap=true := by decide +kernel
theorem certified3323swap : Certified (graph core3323) (root 9) 5 0 :=
  of_native_maps core3323 DegreeTwoThreeSpectrum5870.graph DegreeTwoThreeSpectrum5871.graph
    sourceMap3323swap fusedMap3323swap sourceMap3323swap_checked fusedMap3323swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3323
#print axioms sourceMap3323swap_checked
#print axioms fusedMap3323swap_checked
#print axioms certified3323swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
