/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2889 : Family 10 := level10.get ⟨1290,by decide⟩
def sourceMap2889 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2889 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2889_checked : acceptsGraphIso
    (source (graph core2889) (root 10) 0 4) DegreeTwoThreeSpectrum6564.graph sourceMap2889=true := by decide +kernel
theorem fusedMap2889_checked : acceptsGraphIso
    (fused (graph core2889) (root 10) 0 4) DegreeTwoThreeSpectrum6565.graph fusedMap2889=true := by decide +kernel
theorem certified2889 : Certified (graph core2889) (root 10) 0 4 :=
  of_native_maps core2889 DegreeTwoThreeSpectrum6564.graph DegreeTwoThreeSpectrum6565.graph
    sourceMap2889 fusedMap2889 sourceMap2889_checked fusedMap2889_checked
    DegreeTwoThreeFiniteComparisons.comparison2889
#print axioms sourceMap2889_checked
#print axioms fusedMap2889_checked
#print axioms certified2889
def sourceMap2889swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2889swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2889swap_checked : acceptsGraphIso
    (source (graph core2889) (root 10) 4 0) DegreeTwoThreeSpectrum6564.graph sourceMap2889swap=true := by decide +kernel
theorem fusedMap2889swap_checked : acceptsGraphIso
    (fused (graph core2889) (root 10) 4 0) DegreeTwoThreeSpectrum6565.graph fusedMap2889swap=true := by decide +kernel
theorem certified2889swap : Certified (graph core2889) (root 10) 4 0 :=
  of_native_maps core2889 DegreeTwoThreeSpectrum6564.graph DegreeTwoThreeSpectrum6565.graph
    sourceMap2889swap fusedMap2889swap sourceMap2889swap_checked fusedMap2889swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2889
#print axioms sourceMap2889swap_checked
#print axioms fusedMap2889swap_checked
#print axioms certified2889swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
