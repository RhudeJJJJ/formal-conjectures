/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3226 : Family 8 := level8.get ⟨242,by decide⟩
def sourceMap3226 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3226 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3226_checked : acceptsGraphIso
    (source (graph core3226) (root 8) 0 5) DegreeTwoThreeSpectrum4447.graph sourceMap3226=true := by decide +kernel
theorem fusedMap3226_checked : acceptsGraphIso
    (fused (graph core3226) (root 8) 0 5) DegreeTwoThreeSpectrum4448.graph fusedMap3226=true := by decide +kernel
theorem certified3226 : Certified (graph core3226) (root 8) 0 5 :=
  of_native_maps core3226 DegreeTwoThreeSpectrum4447.graph DegreeTwoThreeSpectrum4448.graph
    sourceMap3226 fusedMap3226 sourceMap3226_checked fusedMap3226_checked
    DegreeTwoThreeFiniteComparisons.comparison3226
#print axioms sourceMap3226_checked
#print axioms fusedMap3226_checked
#print axioms certified3226
def sourceMap3226swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3226swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3226swap_checked : acceptsGraphIso
    (source (graph core3226) (root 8) 5 0) DegreeTwoThreeSpectrum4447.graph sourceMap3226swap=true := by decide +kernel
theorem fusedMap3226swap_checked : acceptsGraphIso
    (fused (graph core3226) (root 8) 5 0) DegreeTwoThreeSpectrum4448.graph fusedMap3226swap=true := by decide +kernel
theorem certified3226swap : Certified (graph core3226) (root 8) 5 0 :=
  of_native_maps core3226 DegreeTwoThreeSpectrum4447.graph DegreeTwoThreeSpectrum4448.graph
    sourceMap3226swap fusedMap3226swap sourceMap3226swap_checked fusedMap3226swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3226
#print axioms sourceMap3226swap_checked
#print axioms fusedMap3226swap_checked
#print axioms certified3226swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
