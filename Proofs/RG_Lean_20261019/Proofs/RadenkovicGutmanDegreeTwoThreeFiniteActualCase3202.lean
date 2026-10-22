/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3202 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap3202 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3202 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3202_checked : acceptsGraphIso
    (source (graph core3202) (root 8) 0 5) DegreeTwoThreeSpectrum4178.graph sourceMap3202=true := by decide +kernel
theorem fusedMap3202_checked : acceptsGraphIso
    (fused (graph core3202) (root 8) 0 5) DegreeTwoThreeSpectrum4179.graph fusedMap3202=true := by decide +kernel
theorem certified3202 : Certified (graph core3202) (root 8) 0 5 :=
  of_native_maps core3202 DegreeTwoThreeSpectrum4178.graph DegreeTwoThreeSpectrum4179.graph
    sourceMap3202 fusedMap3202 sourceMap3202_checked fusedMap3202_checked
    DegreeTwoThreeFiniteComparisons.comparison3202
#print axioms sourceMap3202_checked
#print axioms fusedMap3202_checked
#print axioms certified3202
def sourceMap3202swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3202swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3202swap_checked : acceptsGraphIso
    (source (graph core3202) (root 8) 5 0) DegreeTwoThreeSpectrum4178.graph sourceMap3202swap=true := by decide +kernel
theorem fusedMap3202swap_checked : acceptsGraphIso
    (fused (graph core3202) (root 8) 5 0) DegreeTwoThreeSpectrum4179.graph fusedMap3202swap=true := by decide +kernel
theorem certified3202swap : Certified (graph core3202) (root 8) 5 0 :=
  of_native_maps core3202 DegreeTwoThreeSpectrum4178.graph DegreeTwoThreeSpectrum4179.graph
    sourceMap3202swap fusedMap3202swap sourceMap3202swap_checked fusedMap3202swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3202
#print axioms sourceMap3202swap_checked
#print axioms fusedMap3202swap_checked
#print axioms certified3202swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
