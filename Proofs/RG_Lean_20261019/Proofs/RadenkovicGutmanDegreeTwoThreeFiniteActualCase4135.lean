/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4135 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap4135 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,12,13,14,6,7,8,9,10,11] (sourceLabel 8 2 2 v)
def fusedMap4135 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4135_checked : acceptsGraphIso
    (source (graph core4135) (root 8) 2 2) DegreeTwoThreeSpectrum3357.graph sourceMap4135=true := by decide +kernel
theorem fusedMap4135_checked : acceptsGraphIso
    (fused (graph core4135) (root 8) 2 2) DegreeTwoThreeSpectrum2608.graph fusedMap4135=true := by decide +kernel
theorem certified4135 : Certified (graph core4135) (root 8) 2 2 :=
  of_native_maps core4135 DegreeTwoThreeSpectrum3357.graph DegreeTwoThreeSpectrum2608.graph
    sourceMap4135 fusedMap4135 sourceMap4135_checked fusedMap4135_checked
    DegreeTwoThreeFiniteComparisons.comparison4135
#print axioms sourceMap4135_checked
#print axioms fusedMap4135_checked
#print axioms certified4135
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
