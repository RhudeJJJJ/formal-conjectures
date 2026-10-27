/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4102 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap4102 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,9,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4102 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 2 2 v)
theorem sourceMap4102_checked : acceptsGraphIso
    (source (graph core4102) (root 8) 2 2) DegreeTwoThreeSpectrum2816.graph sourceMap4102=true := by decide +kernel
theorem fusedMap4102_checked : acceptsGraphIso
    (fused (graph core4102) (root 8) 2 2) DegreeTwoThreeSpectrum2434.graph fusedMap4102=true := by decide +kernel
theorem certified4102 : Certified (graph core4102) (root 8) 2 2 :=
  of_native_maps core4102 DegreeTwoThreeSpectrum2816.graph DegreeTwoThreeSpectrum2434.graph
    sourceMap4102 fusedMap4102 sourceMap4102_checked fusedMap4102_checked
    DegreeTwoThreeFiniteComparisons.comparison4102
#print axioms sourceMap4102_checked
#print axioms fusedMap4102_checked
#print axioms certified4102
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
