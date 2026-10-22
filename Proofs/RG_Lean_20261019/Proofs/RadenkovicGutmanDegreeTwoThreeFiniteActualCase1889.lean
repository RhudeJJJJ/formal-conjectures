/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1889 : Family 10 := level10.get ⟨1349,by decide⟩
def sourceMap1889 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1889 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1889_checked : acceptsGraphIso
    (source (graph core1889) (root 10) 0 2) DegreeTwoThreeSpectrum3536.graph sourceMap1889=true := by decide +kernel
theorem fusedMap1889_checked : acceptsGraphIso
    (fused (graph core1889) (root 10) 0 2) DegreeTwoThreeSpectrum3538.graph fusedMap1889=true := by decide +kernel
theorem certified1889 : Certified (graph core1889) (root 10) 0 2 :=
  of_native_maps core1889 DegreeTwoThreeSpectrum3536.graph DegreeTwoThreeSpectrum3538.graph
    sourceMap1889 fusedMap1889 sourceMap1889_checked fusedMap1889_checked
    DegreeTwoThreeFiniteComparisons.comparison1889
#print axioms sourceMap1889_checked
#print axioms fusedMap1889_checked
#print axioms certified1889
def sourceMap1889swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1889swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1889swap_checked : acceptsGraphIso
    (source (graph core1889) (root 10) 2 0) DegreeTwoThreeSpectrum3536.graph sourceMap1889swap=true := by decide +kernel
theorem fusedMap1889swap_checked : acceptsGraphIso
    (fused (graph core1889) (root 10) 2 0) DegreeTwoThreeSpectrum3538.graph fusedMap1889swap=true := by decide +kernel
theorem certified1889swap : Certified (graph core1889) (root 10) 2 0 :=
  of_native_maps core1889 DegreeTwoThreeSpectrum3536.graph DegreeTwoThreeSpectrum3538.graph
    sourceMap1889swap fusedMap1889swap sourceMap1889swap_checked fusedMap1889swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1889
#print axioms sourceMap1889swap_checked
#print axioms fusedMap1889swap_checked
#print axioms certified1889swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
