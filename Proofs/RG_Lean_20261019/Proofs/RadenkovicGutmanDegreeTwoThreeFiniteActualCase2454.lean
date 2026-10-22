/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2454 : Family 10 := level10.get ⟨9,by decide⟩
def sourceMap2454 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,8,9,3,4,5,6,7] (sourceLabel 10 0 4 v)
def fusedMap2454 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 0 4 v)
theorem sourceMap2454_checked : acceptsGraphIso
    (source (graph core2454) (root 10) 0 4) DegreeTwoThreeSpectrum5115.graph sourceMap2454=true := by decide +kernel
theorem fusedMap2454_checked : acceptsGraphIso
    (fused (graph core2454) (root 10) 0 4) DegreeTwoThreeSpectrum4964.graph fusedMap2454=true := by decide +kernel
theorem certified2454 : Certified (graph core2454) (root 10) 0 4 :=
  of_native_maps core2454 DegreeTwoThreeSpectrum5115.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap2454 fusedMap2454 sourceMap2454_checked fusedMap2454_checked
    DegreeTwoThreeFiniteComparisons.comparison2454
#print axioms sourceMap2454_checked
#print axioms fusedMap2454_checked
#print axioms certified2454
def sourceMap2454swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,8,3,4,5,6,7,9] (sourceLabel 10 4 0 v)
def fusedMap2454swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 4 0 v)
theorem sourceMap2454swap_checked : acceptsGraphIso
    (source (graph core2454) (root 10) 4 0) DegreeTwoThreeSpectrum5115.graph sourceMap2454swap=true := by decide +kernel
theorem fusedMap2454swap_checked : acceptsGraphIso
    (fused (graph core2454) (root 10) 4 0) DegreeTwoThreeSpectrum4964.graph fusedMap2454swap=true := by decide +kernel
theorem certified2454swap : Certified (graph core2454) (root 10) 4 0 :=
  of_native_maps core2454 DegreeTwoThreeSpectrum5115.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap2454swap fusedMap2454swap sourceMap2454swap_checked fusedMap2454swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2454
#print axioms sourceMap2454swap_checked
#print axioms fusedMap2454swap_checked
#print axioms certified2454swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
