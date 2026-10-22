/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3063 : Family 10 := level10.get ⟨1740,by decide⟩
def sourceMap3063 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3063 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3063_checked : acceptsGraphIso
    (source (graph core3063) (root 10) 0 4) DegreeTwoThreeSpectrum7381.graph sourceMap3063=true := by decide +kernel
theorem fusedMap3063_checked : acceptsGraphIso
    (fused (graph core3063) (root 10) 0 4) DegreeTwoThreeSpectrum6586.graph fusedMap3063=true := by decide +kernel
theorem certified3063 : Certified (graph core3063) (root 10) 0 4 :=
  of_native_maps core3063 DegreeTwoThreeSpectrum7381.graph DegreeTwoThreeSpectrum6586.graph
    sourceMap3063 fusedMap3063 sourceMap3063_checked fusedMap3063_checked
    DegreeTwoThreeFiniteComparisons.comparison3063
#print axioms sourceMap3063_checked
#print axioms fusedMap3063_checked
#print axioms certified3063
def sourceMap3063swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3063swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3063swap_checked : acceptsGraphIso
    (source (graph core3063) (root 10) 4 0) DegreeTwoThreeSpectrum7381.graph sourceMap3063swap=true := by decide +kernel
theorem fusedMap3063swap_checked : acceptsGraphIso
    (fused (graph core3063) (root 10) 4 0) DegreeTwoThreeSpectrum6586.graph fusedMap3063swap=true := by decide +kernel
theorem certified3063swap : Certified (graph core3063) (root 10) 4 0 :=
  of_native_maps core3063 DegreeTwoThreeSpectrum7381.graph DegreeTwoThreeSpectrum6586.graph
    sourceMap3063swap fusedMap3063swap sourceMap3063swap_checked fusedMap3063swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3063
#print axioms sourceMap3063swap_checked
#print axioms fusedMap3063swap_checked
#print axioms certified3063swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
