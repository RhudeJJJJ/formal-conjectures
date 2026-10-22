/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1373 : Family 9 := level9.get ⟨530,by decide⟩
def sourceMap1373 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,9,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1373 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 0 2 v)
theorem sourceMap1373_checked : acceptsGraphIso
    (source (graph core1373) (root 9) 0 2) DegreeTwoThreeSpectrum2096.graph sourceMap1373=true := by decide +kernel
theorem fusedMap1373_checked : acceptsGraphIso
    (fused (graph core1373) (root 9) 0 2) DegreeTwoThreeSpectrum2236.graph fusedMap1373=true := by decide +kernel
theorem certified1373 : Certified (graph core1373) (root 9) 0 2 :=
  of_native_maps core1373 DegreeTwoThreeSpectrum2096.graph DegreeTwoThreeSpectrum2236.graph
    sourceMap1373 fusedMap1373 sourceMap1373_checked fusedMap1373_checked
    DegreeTwoThreeFiniteComparisons.comparison1373
#print axioms sourceMap1373_checked
#print axioms fusedMap1373_checked
#print axioms certified1373
def sourceMap1373swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,6,7,8,9] (sourceLabel 9 2 0 v)
def fusedMap1373swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 2 0 v)
theorem sourceMap1373swap_checked : acceptsGraphIso
    (source (graph core1373) (root 9) 2 0) DegreeTwoThreeSpectrum2096.graph sourceMap1373swap=true := by decide +kernel
theorem fusedMap1373swap_checked : acceptsGraphIso
    (fused (graph core1373) (root 9) 2 0) DegreeTwoThreeSpectrum2236.graph fusedMap1373swap=true := by decide +kernel
theorem certified1373swap : Certified (graph core1373) (root 9) 2 0 :=
  of_native_maps core1373 DegreeTwoThreeSpectrum2096.graph DegreeTwoThreeSpectrum2236.graph
    sourceMap1373swap fusedMap1373swap sourceMap1373swap_checked fusedMap1373swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1373
#print axioms sourceMap1373swap_checked
#print axioms fusedMap1373swap_checked
#print axioms certified1373swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
