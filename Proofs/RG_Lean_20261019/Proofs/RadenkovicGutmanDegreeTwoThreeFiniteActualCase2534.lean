/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2534 : Family 10 := level10.get ⟨332,by decide⟩
def sourceMap2534 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2534 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2534_checked : acceptsGraphIso
    (source (graph core2534) (root 10) 0 4) DegreeTwoThreeSpectrum5571.graph sourceMap2534=true := by decide +kernel
theorem fusedMap2534_checked : acceptsGraphIso
    (fused (graph core2534) (root 10) 0 4) DegreeTwoThreeSpectrum5572.graph fusedMap2534=true := by decide +kernel
theorem certified2534 : Certified (graph core2534) (root 10) 0 4 :=
  of_native_maps core2534 DegreeTwoThreeSpectrum5571.graph DegreeTwoThreeSpectrum5572.graph
    sourceMap2534 fusedMap2534 sourceMap2534_checked fusedMap2534_checked
    DegreeTwoThreeFiniteComparisons.comparison2534
#print axioms sourceMap2534_checked
#print axioms fusedMap2534_checked
#print axioms certified2534
def sourceMap2534swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2534swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2534swap_checked : acceptsGraphIso
    (source (graph core2534) (root 10) 4 0) DegreeTwoThreeSpectrum5571.graph sourceMap2534swap=true := by decide +kernel
theorem fusedMap2534swap_checked : acceptsGraphIso
    (fused (graph core2534) (root 10) 4 0) DegreeTwoThreeSpectrum5572.graph fusedMap2534swap=true := by decide +kernel
theorem certified2534swap : Certified (graph core2534) (root 10) 4 0 :=
  of_native_maps core2534 DegreeTwoThreeSpectrum5571.graph DegreeTwoThreeSpectrum5572.graph
    sourceMap2534swap fusedMap2534swap sourceMap2534swap_checked fusedMap2534swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2534
#print axioms sourceMap2534swap_checked
#print axioms fusedMap2534swap_checked
#print axioms certified2534swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
