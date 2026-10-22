/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3534 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap3534 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3534 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3534_checked : acceptsGraphIso
    (source (graph core3534) (root 7) 0 6) DegreeTwoThreeSpectrum4491.graph sourceMap3534=true := by decide +kernel
theorem fusedMap3534_checked : acceptsGraphIso
    (fused (graph core3534) (root 7) 0 6) DegreeTwoThreeSpectrum4019.graph fusedMap3534=true := by decide +kernel
theorem certified3534 : Certified (graph core3534) (root 7) 0 6 :=
  of_native_maps core3534 DegreeTwoThreeSpectrum4491.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap3534 fusedMap3534 sourceMap3534_checked fusedMap3534_checked
    DegreeTwoThreeFiniteComparisons.comparison3534
#print axioms sourceMap3534_checked
#print axioms fusedMap3534_checked
#print axioms certified3534
def sourceMap3534swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3534swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3534swap_checked : acceptsGraphIso
    (source (graph core3534) (root 7) 6 0) DegreeTwoThreeSpectrum4491.graph sourceMap3534swap=true := by decide +kernel
theorem fusedMap3534swap_checked : acceptsGraphIso
    (fused (graph core3534) (root 7) 6 0) DegreeTwoThreeSpectrum4019.graph fusedMap3534swap=true := by decide +kernel
theorem certified3534swap : Certified (graph core3534) (root 7) 6 0 :=
  of_native_maps core3534 DegreeTwoThreeSpectrum4491.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap3534swap fusedMap3534swap sourceMap3534swap_checked fusedMap3534swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3534
#print axioms sourceMap3534swap_checked
#print axioms fusedMap3534swap_checked
#print axioms certified3534swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
