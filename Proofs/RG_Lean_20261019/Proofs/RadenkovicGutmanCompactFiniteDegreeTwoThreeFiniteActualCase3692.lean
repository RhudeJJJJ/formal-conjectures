/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3692 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap3692 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3692 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3692_checked : acceptsGraphIso
    (source (graph core3692) (root 7) 0 7) DegreeTwoThreeSpectrum5501.graph sourceMap3692=true := by decide +kernel
theorem fusedMap3692_checked : acceptsGraphIso
    (fused (graph core3692) (root 7) 0 7) DegreeTwoThreeSpectrum5504.graph fusedMap3692=true := by decide +kernel
theorem certified3692 : Certified (graph core3692) (root 7) 0 7 :=
  of_native_maps core3692 DegreeTwoThreeSpectrum5501.graph DegreeTwoThreeSpectrum5504.graph
    sourceMap3692 fusedMap3692 sourceMap3692_checked fusedMap3692_checked
    DegreeTwoThreeFiniteComparisons.comparison3692
#print axioms sourceMap3692_checked
#print axioms fusedMap3692_checked
#print axioms certified3692
def sourceMap3692swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3692swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3692swap_checked : acceptsGraphIso
    (source (graph core3692) (root 7) 7 0) DegreeTwoThreeSpectrum5501.graph sourceMap3692swap=true := by decide +kernel
theorem fusedMap3692swap_checked : acceptsGraphIso
    (fused (graph core3692) (root 7) 7 0) DegreeTwoThreeSpectrum5504.graph fusedMap3692swap=true := by decide +kernel
theorem certified3692swap : Certified (graph core3692) (root 7) 7 0 :=
  of_native_maps core3692 DegreeTwoThreeSpectrum5501.graph DegreeTwoThreeSpectrum5504.graph
    sourceMap3692swap fusedMap3692swap sourceMap3692swap_checked fusedMap3692swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3692
#print axioms sourceMap3692swap_checked
#print axioms fusedMap3692swap_checked
#print axioms certified3692swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
