/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3716 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap3716 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3716 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3716_checked : acceptsGraphIso
    (source (graph core3716) (root 6) 0 8) DegreeTwoThreeSpectrum5272.graph sourceMap3716=true := by decide +kernel
theorem fusedMap3716_checked : acceptsGraphIso
    (fused (graph core3716) (root 6) 0 8) DegreeTwoThreeSpectrum4975.graph fusedMap3716=true := by decide +kernel
theorem certified3716 : Certified (graph core3716) (root 6) 0 8 :=
  of_native_maps core3716 DegreeTwoThreeSpectrum5272.graph DegreeTwoThreeSpectrum4975.graph
    sourceMap3716 fusedMap3716 sourceMap3716_checked fusedMap3716_checked
    DegreeTwoThreeFiniteComparisons.comparison3716
#print axioms sourceMap3716_checked
#print axioms fusedMap3716_checked
#print axioms certified3716
def sourceMap3716swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3716swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3716swap_checked : acceptsGraphIso
    (source (graph core3716) (root 6) 8 0) DegreeTwoThreeSpectrum5272.graph sourceMap3716swap=true := by decide +kernel
theorem fusedMap3716swap_checked : acceptsGraphIso
    (fused (graph core3716) (root 6) 8 0) DegreeTwoThreeSpectrum4975.graph fusedMap3716swap=true := by decide +kernel
theorem certified3716swap : Certified (graph core3716) (root 6) 8 0 :=
  of_native_maps core3716 DegreeTwoThreeSpectrum5272.graph DegreeTwoThreeSpectrum4975.graph
    sourceMap3716swap fusedMap3716swap sourceMap3716swap_checked fusedMap3716swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3716
#print axioms sourceMap3716swap_checked
#print axioms fusedMap3716swap_checked
#print axioms certified3716swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
