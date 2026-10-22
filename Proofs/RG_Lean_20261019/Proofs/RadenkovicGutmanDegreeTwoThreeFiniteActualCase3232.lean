/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3232 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap3232 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3232 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3232_checked : acceptsGraphIso
    (source (graph core3232) (root 8) 0 5) DegreeTwoThreeSpectrum4668.graph sourceMap3232=true := by decide +kernel
theorem fusedMap3232_checked : acceptsGraphIso
    (fused (graph core3232) (root 8) 0 5) DegreeTwoThreeSpectrum4171.graph fusedMap3232=true := by decide +kernel
theorem certified3232 : Certified (graph core3232) (root 8) 0 5 :=
  of_native_maps core3232 DegreeTwoThreeSpectrum4668.graph DegreeTwoThreeSpectrum4171.graph
    sourceMap3232 fusedMap3232 sourceMap3232_checked fusedMap3232_checked
    DegreeTwoThreeFiniteComparisons.comparison3232
#print axioms sourceMap3232_checked
#print axioms fusedMap3232_checked
#print axioms certified3232
def sourceMap3232swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,11] (sourceLabel 8 5 0 v)
def fusedMap3232swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3232swap_checked : acceptsGraphIso
    (source (graph core3232) (root 8) 5 0) DegreeTwoThreeSpectrum4668.graph sourceMap3232swap=true := by decide +kernel
theorem fusedMap3232swap_checked : acceptsGraphIso
    (fused (graph core3232) (root 8) 5 0) DegreeTwoThreeSpectrum4171.graph fusedMap3232swap=true := by decide +kernel
theorem certified3232swap : Certified (graph core3232) (root 8) 5 0 :=
  of_native_maps core3232 DegreeTwoThreeSpectrum4668.graph DegreeTwoThreeSpectrum4171.graph
    sourceMap3232swap fusedMap3232swap sourceMap3232swap_checked fusedMap3232swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3232
#print axioms sourceMap3232swap_checked
#print axioms fusedMap3232swap_checked
#print axioms certified3232swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
