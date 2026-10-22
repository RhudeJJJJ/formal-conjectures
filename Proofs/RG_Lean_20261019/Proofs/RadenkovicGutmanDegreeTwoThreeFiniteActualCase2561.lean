/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2561 : Family 10 := level10.get ⟨419,by decide⟩
def sourceMap2561 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2561 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2561_checked : acceptsGraphIso
    (source (graph core2561) (root 10) 0 4) DegreeTwoThreeSpectrum5803.graph sourceMap2561=true := by decide +kernel
theorem fusedMap2561_checked : acceptsGraphIso
    (fused (graph core2561) (root 10) 0 4) DegreeTwoThreeSpectrum5804.graph fusedMap2561=true := by decide +kernel
theorem certified2561 : Certified (graph core2561) (root 10) 0 4 :=
  of_native_maps core2561 DegreeTwoThreeSpectrum5803.graph DegreeTwoThreeSpectrum5804.graph
    sourceMap2561 fusedMap2561 sourceMap2561_checked fusedMap2561_checked
    DegreeTwoThreeFiniteComparisons.comparison2561
#print axioms sourceMap2561_checked
#print axioms fusedMap2561_checked
#print axioms certified2561
def sourceMap2561swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2561swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2561swap_checked : acceptsGraphIso
    (source (graph core2561) (root 10) 4 0) DegreeTwoThreeSpectrum5803.graph sourceMap2561swap=true := by decide +kernel
theorem fusedMap2561swap_checked : acceptsGraphIso
    (fused (graph core2561) (root 10) 4 0) DegreeTwoThreeSpectrum5804.graph fusedMap2561swap=true := by decide +kernel
theorem certified2561swap : Certified (graph core2561) (root 10) 4 0 :=
  of_native_maps core2561 DegreeTwoThreeSpectrum5803.graph DegreeTwoThreeSpectrum5804.graph
    sourceMap2561swap fusedMap2561swap sourceMap2561swap_checked fusedMap2561swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2561
#print axioms sourceMap2561swap_checked
#print axioms fusedMap2561swap_checked
#print axioms certified2561swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
