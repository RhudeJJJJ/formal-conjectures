/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3530 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap3530 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3530 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3530_checked : acceptsGraphIso
    (source (graph core3530) (root 7) 0 6) DegreeTwoThreeSpectrum4421.graph sourceMap3530=true := by decide +kernel
theorem fusedMap3530_checked : acceptsGraphIso
    (fused (graph core3530) (root 7) 0 6) DegreeTwoThreeSpectrum3987.graph fusedMap3530=true := by decide +kernel
theorem certified3530 : Certified (graph core3530) (root 7) 0 6 :=
  of_native_maps core3530 DegreeTwoThreeSpectrum4421.graph DegreeTwoThreeSpectrum3987.graph
    sourceMap3530 fusedMap3530 sourceMap3530_checked fusedMap3530_checked
    DegreeTwoThreeFiniteComparisons.comparison3530
#print axioms sourceMap3530_checked
#print axioms fusedMap3530_checked
#print axioms certified3530
def sourceMap3530swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3530swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3530swap_checked : acceptsGraphIso
    (source (graph core3530) (root 7) 6 0) DegreeTwoThreeSpectrum4421.graph sourceMap3530swap=true := by decide +kernel
theorem fusedMap3530swap_checked : acceptsGraphIso
    (fused (graph core3530) (root 7) 6 0) DegreeTwoThreeSpectrum3987.graph fusedMap3530swap=true := by decide +kernel
theorem certified3530swap : Certified (graph core3530) (root 7) 6 0 :=
  of_native_maps core3530 DegreeTwoThreeSpectrum4421.graph DegreeTwoThreeSpectrum3987.graph
    sourceMap3530swap fusedMap3530swap sourceMap3530swap_checked fusedMap3530swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3530
#print axioms sourceMap3530swap_checked
#print axioms fusedMap3530swap_checked
#print axioms certified3530swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
