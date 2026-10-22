/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2552 : Family 10 := level10.get ⟨388,by decide⟩
def sourceMap2552 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2552 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2552_checked : acceptsGraphIso
    (source (graph core2552) (root 10) 0 4) DegreeTwoThreeSpectrum5722.graph sourceMap2552=true := by decide +kernel
theorem fusedMap2552_checked : acceptsGraphIso
    (fused (graph core2552) (root 10) 0 4) DegreeTwoThreeSpectrum5724.graph fusedMap2552=true := by decide +kernel
theorem certified2552 : Certified (graph core2552) (root 10) 0 4 :=
  of_native_maps core2552 DegreeTwoThreeSpectrum5722.graph DegreeTwoThreeSpectrum5724.graph
    sourceMap2552 fusedMap2552 sourceMap2552_checked fusedMap2552_checked
    DegreeTwoThreeFiniteComparisons.comparison2552
#print axioms sourceMap2552_checked
#print axioms fusedMap2552_checked
#print axioms certified2552
def sourceMap2552swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2552swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2552swap_checked : acceptsGraphIso
    (source (graph core2552) (root 10) 4 0) DegreeTwoThreeSpectrum5722.graph sourceMap2552swap=true := by decide +kernel
theorem fusedMap2552swap_checked : acceptsGraphIso
    (fused (graph core2552) (root 10) 4 0) DegreeTwoThreeSpectrum5724.graph fusedMap2552swap=true := by decide +kernel
theorem certified2552swap : Certified (graph core2552) (root 10) 4 0 :=
  of_native_maps core2552 DegreeTwoThreeSpectrum5722.graph DegreeTwoThreeSpectrum5724.graph
    sourceMap2552swap fusedMap2552swap sourceMap2552swap_checked fusedMap2552swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2552
#print axioms sourceMap2552swap_checked
#print axioms fusedMap2552swap_checked
#print axioms certified2552swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
