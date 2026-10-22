/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3047 : Family 10 := level10.get ⟨1700,by decide⟩
def sourceMap3047 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3047 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3047_checked : acceptsGraphIso
    (source (graph core3047) (root 10) 0 4) DegreeTwoThreeSpectrum7322.graph sourceMap3047=true := by decide +kernel
theorem fusedMap3047_checked : acceptsGraphIso
    (fused (graph core3047) (root 10) 0 4) DegreeTwoThreeSpectrum6468.graph fusedMap3047=true := by decide +kernel
theorem certified3047 : Certified (graph core3047) (root 10) 0 4 :=
  of_native_maps core3047 DegreeTwoThreeSpectrum7322.graph DegreeTwoThreeSpectrum6468.graph
    sourceMap3047 fusedMap3047 sourceMap3047_checked fusedMap3047_checked
    DegreeTwoThreeFiniteComparisons.comparison3047
#print axioms sourceMap3047_checked
#print axioms fusedMap3047_checked
#print axioms certified3047
def sourceMap3047swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3047swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3047swap_checked : acceptsGraphIso
    (source (graph core3047) (root 10) 4 0) DegreeTwoThreeSpectrum7322.graph sourceMap3047swap=true := by decide +kernel
theorem fusedMap3047swap_checked : acceptsGraphIso
    (fused (graph core3047) (root 10) 4 0) DegreeTwoThreeSpectrum6468.graph fusedMap3047swap=true := by decide +kernel
theorem certified3047swap : Certified (graph core3047) (root 10) 4 0 :=
  of_native_maps core3047 DegreeTwoThreeSpectrum7322.graph DegreeTwoThreeSpectrum6468.graph
    sourceMap3047swap fusedMap3047swap sourceMap3047swap_checked fusedMap3047swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3047
#print axioms sourceMap3047swap_checked
#print axioms fusedMap3047swap_checked
#print axioms certified3047swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
