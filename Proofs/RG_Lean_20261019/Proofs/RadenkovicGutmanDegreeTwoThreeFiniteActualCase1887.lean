/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1887 : Family 10 := level10.get ⟨1340,by decide⟩
def sourceMap1887 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1887 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1887_checked : acceptsGraphIso
    (source (graph core1887) (root 10) 0 2) DegreeTwoThreeSpectrum3518.graph sourceMap1887=true := by decide +kernel
theorem fusedMap1887_checked : acceptsGraphIso
    (fused (graph core1887) (root 10) 0 2) DegreeTwoThreeSpectrum3527.graph fusedMap1887=true := by decide +kernel
theorem certified1887 : Certified (graph core1887) (root 10) 0 2 :=
  of_native_maps core1887 DegreeTwoThreeSpectrum3518.graph DegreeTwoThreeSpectrum3527.graph
    sourceMap1887 fusedMap1887 sourceMap1887_checked fusedMap1887_checked
    DegreeTwoThreeFiniteComparisons.comparison1887
#print axioms sourceMap1887_checked
#print axioms fusedMap1887_checked
#print axioms certified1887
def sourceMap1887swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1887swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1887swap_checked : acceptsGraphIso
    (source (graph core1887) (root 10) 2 0) DegreeTwoThreeSpectrum3518.graph sourceMap1887swap=true := by decide +kernel
theorem fusedMap1887swap_checked : acceptsGraphIso
    (fused (graph core1887) (root 10) 2 0) DegreeTwoThreeSpectrum3527.graph fusedMap1887swap=true := by decide +kernel
theorem certified1887swap : Certified (graph core1887) (root 10) 2 0 :=
  of_native_maps core1887 DegreeTwoThreeSpectrum3518.graph DegreeTwoThreeSpectrum3527.graph
    sourceMap1887swap fusedMap1887swap sourceMap1887swap_checked fusedMap1887swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1887
#print axioms sourceMap1887swap_checked
#print axioms fusedMap1887swap_checked
#print axioms certified1887swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
