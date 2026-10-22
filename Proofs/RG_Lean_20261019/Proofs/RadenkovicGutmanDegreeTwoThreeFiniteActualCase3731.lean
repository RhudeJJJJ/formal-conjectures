/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3731 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3731 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (sourceLabel 5 0 9 v)
def fusedMap3731 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 5 0 9 v)
theorem sourceMap3731_checked : acceptsGraphIso
    (source (graph core3731) (root 5) 0 9) DegreeTwoThreeSpectrum5091.graph sourceMap3731=true := by decide +kernel
theorem fusedMap3731_checked : acceptsGraphIso
    (fused (graph core3731) (root 5) 0 9) DegreeTwoThreeSpectrum4962.graph fusedMap3731=true := by decide +kernel
theorem certified3731 : Certified (graph core3731) (root 5) 0 9 :=
  of_native_maps core3731 DegreeTwoThreeSpectrum5091.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap3731 fusedMap3731 sourceMap3731_checked fusedMap3731_checked
    DegreeTwoThreeFiniteComparisons.comparison3731
#print axioms sourceMap3731_checked
#print axioms fusedMap3731_checked
#print axioms certified3731
def sourceMap3731swap : (Vertices 5 ⊕ Fin 10 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 5 9 0 v)
def fusedMap3731swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 5 9 0 v)
theorem sourceMap3731swap_checked : acceptsGraphIso
    (source (graph core3731) (root 5) 9 0) DegreeTwoThreeSpectrum5091.graph sourceMap3731swap=true := by decide +kernel
theorem fusedMap3731swap_checked : acceptsGraphIso
    (fused (graph core3731) (root 5) 9 0) DegreeTwoThreeSpectrum4962.graph fusedMap3731swap=true := by decide +kernel
theorem certified3731swap : Certified (graph core3731) (root 5) 9 0 :=
  of_native_maps core3731 DegreeTwoThreeSpectrum5091.graph DegreeTwoThreeSpectrum4962.graph
    sourceMap3731swap fusedMap3731swap sourceMap3731swap_checked fusedMap3731swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3731
#print axioms sourceMap3731swap_checked
#print axioms fusedMap3731swap_checked
#print axioms certified3731swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
