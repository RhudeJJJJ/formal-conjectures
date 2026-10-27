/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4804 : Family 10 := level10.get ⟨1142,by decide⟩
def sourceMap4804 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4804 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4804_checked : acceptsGraphIso
    (source (graph core4804) (root 10) 2 2) DegreeTwoThreeSpectrum7224.graph sourceMap4804=true := by decide +kernel
theorem fusedMap4804_checked : acceptsGraphIso
    (fused (graph core4804) (root 10) 2 2) DegreeTwoThreeSpectrum6271.graph fusedMap4804=true := by decide +kernel
theorem certified4804 : Certified (graph core4804) (root 10) 2 2 :=
  of_native_maps core4804 DegreeTwoThreeSpectrum7224.graph DegreeTwoThreeSpectrum6271.graph
    sourceMap4804 fusedMap4804 sourceMap4804_checked fusedMap4804_checked
    DegreeTwoThreeFiniteComparisons.comparison4804
#print axioms sourceMap4804_checked
#print axioms fusedMap4804_checked
#print axioms certified4804
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
