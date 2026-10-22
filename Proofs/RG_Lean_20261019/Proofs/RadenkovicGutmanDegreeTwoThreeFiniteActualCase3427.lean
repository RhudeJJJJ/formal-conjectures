/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3427 : Family 9 := level9.get ⟨558,by decide⟩
def sourceMap3427 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3427 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3427_checked : acceptsGraphIso
    (source (graph core3427) (root 9) 0 5) DegreeTwoThreeSpectrum6026.graph sourceMap3427=true := by decide +kernel
theorem fusedMap3427_checked : acceptsGraphIso
    (fused (graph core3427) (root 9) 0 5) DegreeTwoThreeSpectrum6027.graph fusedMap3427=true := by decide +kernel
theorem certified3427 : Certified (graph core3427) (root 9) 0 5 :=
  of_native_maps core3427 DegreeTwoThreeSpectrum6026.graph DegreeTwoThreeSpectrum6027.graph
    sourceMap3427 fusedMap3427 sourceMap3427_checked fusedMap3427_checked
    DegreeTwoThreeFiniteComparisons.comparison3427
#print axioms sourceMap3427_checked
#print axioms fusedMap3427_checked
#print axioms certified3427
def sourceMap3427swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3427swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3427swap_checked : acceptsGraphIso
    (source (graph core3427) (root 9) 5 0) DegreeTwoThreeSpectrum6026.graph sourceMap3427swap=true := by decide +kernel
theorem fusedMap3427swap_checked : acceptsGraphIso
    (fused (graph core3427) (root 9) 5 0) DegreeTwoThreeSpectrum6027.graph fusedMap3427swap=true := by decide +kernel
theorem certified3427swap : Certified (graph core3427) (root 9) 5 0 :=
  of_native_maps core3427 DegreeTwoThreeSpectrum6026.graph DegreeTwoThreeSpectrum6027.graph
    sourceMap3427swap fusedMap3427swap sourceMap3427swap_checked fusedMap3427swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3427
#print axioms sourceMap3427swap_checked
#print axioms fusedMap3427swap_checked
#print axioms certified3427swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
