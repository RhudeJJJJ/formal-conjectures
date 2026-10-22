/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1920 : Family 10 := level10.get ⟨1422,by decide⟩
def sourceMap1920 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1920 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1920_checked : acceptsGraphIso
    (source (graph core1920) (root 10) 0 2) DegreeTwoThreeSpectrum3643.graph sourceMap1920=true := by decide +kernel
theorem fusedMap1920_checked : acceptsGraphIso
    (fused (graph core1920) (root 10) 0 2) DegreeTwoThreeSpectrum3645.graph fusedMap1920=true := by decide +kernel
theorem certified1920 : Certified (graph core1920) (root 10) 0 2 :=
  of_native_maps core1920 DegreeTwoThreeSpectrum3643.graph DegreeTwoThreeSpectrum3645.graph
    sourceMap1920 fusedMap1920 sourceMap1920_checked fusedMap1920_checked
    DegreeTwoThreeFiniteComparisons.comparison1920
#print axioms sourceMap1920_checked
#print axioms fusedMap1920_checked
#print axioms certified1920
def sourceMap1920swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1920swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1920swap_checked : acceptsGraphIso
    (source (graph core1920) (root 10) 2 0) DegreeTwoThreeSpectrum3643.graph sourceMap1920swap=true := by decide +kernel
theorem fusedMap1920swap_checked : acceptsGraphIso
    (fused (graph core1920) (root 10) 2 0) DegreeTwoThreeSpectrum3645.graph fusedMap1920swap=true := by decide +kernel
theorem certified1920swap : Certified (graph core1920) (root 10) 2 0 :=
  of_native_maps core1920 DegreeTwoThreeSpectrum3643.graph DegreeTwoThreeSpectrum3645.graph
    sourceMap1920swap fusedMap1920swap sourceMap1920swap_checked fusedMap1920swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1920
#print axioms sourceMap1920swap_checked
#print axioms fusedMap1920swap_checked
#print axioms certified1920swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
