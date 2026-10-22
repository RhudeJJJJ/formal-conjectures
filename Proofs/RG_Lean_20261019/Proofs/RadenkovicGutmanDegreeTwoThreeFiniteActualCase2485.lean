/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2485 : Family 10 := level10.get ⟨158,by decide⟩
def sourceMap2485 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2485 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2485_checked : acceptsGraphIso
    (source (graph core2485) (root 10) 0 4) DegreeTwoThreeSpectrum5899.graph sourceMap2485=true := by decide +kernel
theorem fusedMap2485_checked : acceptsGraphIso
    (fused (graph core2485) (root 10) 0 4) DegreeTwoThreeSpectrum5095.graph fusedMap2485=true := by decide +kernel
theorem certified2485 : Certified (graph core2485) (root 10) 0 4 :=
  of_native_maps core2485 DegreeTwoThreeSpectrum5899.graph DegreeTwoThreeSpectrum5095.graph
    sourceMap2485 fusedMap2485 sourceMap2485_checked fusedMap2485_checked
    DegreeTwoThreeFiniteComparisons.comparison2485
#print axioms sourceMap2485_checked
#print axioms fusedMap2485_checked
#print axioms certified2485
def sourceMap2485swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2485swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2485swap_checked : acceptsGraphIso
    (source (graph core2485) (root 10) 4 0) DegreeTwoThreeSpectrum5899.graph sourceMap2485swap=true := by decide +kernel
theorem fusedMap2485swap_checked : acceptsGraphIso
    (fused (graph core2485) (root 10) 4 0) DegreeTwoThreeSpectrum5095.graph fusedMap2485swap=true := by decide +kernel
theorem certified2485swap : Certified (graph core2485) (root 10) 4 0 :=
  of_native_maps core2485 DegreeTwoThreeSpectrum5899.graph DegreeTwoThreeSpectrum5095.graph
    sourceMap2485swap fusedMap2485swap sourceMap2485swap_checked fusedMap2485swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2485
#print axioms sourceMap2485swap_checked
#print axioms fusedMap2485swap_checked
#print axioms certified2485swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
