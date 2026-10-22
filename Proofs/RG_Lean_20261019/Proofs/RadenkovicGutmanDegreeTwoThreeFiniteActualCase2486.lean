/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2486 : Family 10 := level10.get ⟨161,by decide⟩
def sourceMap2486 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,15,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2486 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2486_checked : acceptsGraphIso
    (source (graph core2486) (root 10) 0 4) DegreeTwoThreeSpectrum5905.graph sourceMap2486=true := by decide +kernel
theorem fusedMap2486_checked : acceptsGraphIso
    (fused (graph core2486) (root 10) 0 4) DegreeTwoThreeSpectrum5099.graph fusedMap2486=true := by decide +kernel
theorem certified2486 : Certified (graph core2486) (root 10) 0 4 :=
  of_native_maps core2486 DegreeTwoThreeSpectrum5905.graph DegreeTwoThreeSpectrum5099.graph
    sourceMap2486 fusedMap2486 sourceMap2486_checked fusedMap2486_checked
    DegreeTwoThreeFiniteComparisons.comparison2486
#print axioms sourceMap2486_checked
#print axioms fusedMap2486_checked
#print axioms certified2486
def sourceMap2486swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,9,10,11,12,13,15] (sourceLabel 10 4 0 v)
def fusedMap2486swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2486swap_checked : acceptsGraphIso
    (source (graph core2486) (root 10) 4 0) DegreeTwoThreeSpectrum5905.graph sourceMap2486swap=true := by decide +kernel
theorem fusedMap2486swap_checked : acceptsGraphIso
    (fused (graph core2486) (root 10) 4 0) DegreeTwoThreeSpectrum5099.graph fusedMap2486swap=true := by decide +kernel
theorem certified2486swap : Certified (graph core2486) (root 10) 4 0 :=
  of_native_maps core2486 DegreeTwoThreeSpectrum5905.graph DegreeTwoThreeSpectrum5099.graph
    sourceMap2486swap fusedMap2486swap sourceMap2486swap_checked fusedMap2486swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2486
#print axioms sourceMap2486swap_checked
#print axioms fusedMap2486swap_checked
#print axioms certified2486swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
