/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3161 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap3161 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3161 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3161_checked : acceptsGraphIso
    (source (graph core3161) (root 8) 0 5) DegreeTwoThreeSpectrum4129.graph sourceMap3161=true := by decide +kernel
theorem fusedMap3161_checked : acceptsGraphIso
    (fused (graph core3161) (root 8) 0 5) DegreeTwoThreeSpectrum4130.graph fusedMap3161=true := by decide +kernel
theorem certified3161 : Certified (graph core3161) (root 8) 0 5 :=
  of_native_maps core3161 DegreeTwoThreeSpectrum4129.graph DegreeTwoThreeSpectrum4130.graph
    sourceMap3161 fusedMap3161 sourceMap3161_checked fusedMap3161_checked
    DegreeTwoThreeFiniteComparisons.comparison3161
#print axioms sourceMap3161_checked
#print axioms fusedMap3161_checked
#print axioms certified3161
def sourceMap3161swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3161swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3161swap_checked : acceptsGraphIso
    (source (graph core3161) (root 8) 5 0) DegreeTwoThreeSpectrum4129.graph sourceMap3161swap=true := by decide +kernel
theorem fusedMap3161swap_checked : acceptsGraphIso
    (fused (graph core3161) (root 8) 5 0) DegreeTwoThreeSpectrum4130.graph fusedMap3161swap=true := by decide +kernel
theorem certified3161swap : Certified (graph core3161) (root 8) 5 0 :=
  of_native_maps core3161 DegreeTwoThreeSpectrum4129.graph DegreeTwoThreeSpectrum4130.graph
    sourceMap3161swap fusedMap3161swap sourceMap3161swap_checked fusedMap3161swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3161
#print axioms sourceMap3161swap_checked
#print axioms fusedMap3161swap_checked
#print axioms certified3161swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
