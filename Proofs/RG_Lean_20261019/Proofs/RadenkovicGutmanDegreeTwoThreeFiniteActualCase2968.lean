/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2968 : Family 10 := level10.get ⟨1475,by decide⟩
def sourceMap2968 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2968 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2968_checked : acceptsGraphIso
    (source (graph core2968) (root 10) 0 4) DegreeTwoThreeSpectrum6960.graph sourceMap2968=true := by decide +kernel
theorem fusedMap2968_checked : acceptsGraphIso
    (fused (graph core2968) (root 10) 0 4) DegreeTwoThreeSpectrum6961.graph fusedMap2968=true := by decide +kernel
theorem certified2968 : Certified (graph core2968) (root 10) 0 4 :=
  of_native_maps core2968 DegreeTwoThreeSpectrum6960.graph DegreeTwoThreeSpectrum6961.graph
    sourceMap2968 fusedMap2968 sourceMap2968_checked fusedMap2968_checked
    DegreeTwoThreeFiniteComparisons.comparison2968
#print axioms sourceMap2968_checked
#print axioms fusedMap2968_checked
#print axioms certified2968
def sourceMap2968swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2968swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2968swap_checked : acceptsGraphIso
    (source (graph core2968) (root 10) 4 0) DegreeTwoThreeSpectrum6960.graph sourceMap2968swap=true := by decide +kernel
theorem fusedMap2968swap_checked : acceptsGraphIso
    (fused (graph core2968) (root 10) 4 0) DegreeTwoThreeSpectrum6961.graph fusedMap2968swap=true := by decide +kernel
theorem certified2968swap : Certified (graph core2968) (root 10) 4 0 :=
  of_native_maps core2968 DegreeTwoThreeSpectrum6960.graph DegreeTwoThreeSpectrum6961.graph
    sourceMap2968swap fusedMap2968swap sourceMap2968swap_checked fusedMap2968swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2968
#print axioms sourceMap2968swap_checked
#print axioms fusedMap2968swap_checked
#print axioms certified2968swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
