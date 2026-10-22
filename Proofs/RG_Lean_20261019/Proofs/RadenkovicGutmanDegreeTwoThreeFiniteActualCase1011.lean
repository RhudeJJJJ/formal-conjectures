/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1011 : Family 10 := level10.get ⟨1746,by decide⟩
def sourceMap1011 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap1011 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap1011_checked : acceptsGraphIso
    (source (graph core1011) (root 10) 0 0) DegreeTwoThreeSpectrum1413.graph sourceMap1011=true := by decide +kernel
theorem fusedMap1011_checked : acceptsGraphIso
    (fused (graph core1011) (root 10) 0 0) DegreeTwoThreeSpectrum1389.graph fusedMap1011=true := by decide +kernel
theorem certified1011 : Certified (graph core1011) (root 10) 0 0 :=
  of_native_maps core1011 DegreeTwoThreeSpectrum1413.graph DegreeTwoThreeSpectrum1389.graph
    sourceMap1011 fusedMap1011 sourceMap1011_checked fusedMap1011_checked
    DegreeTwoThreeFiniteComparisons.comparison1011
#print axioms sourceMap1011_checked
#print axioms fusedMap1011_checked
#print axioms certified1011
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
