/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4143 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap4143 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4143 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4143_checked : acceptsGraphIso
    (source (graph core4143) (root 8) 2 2) DegreeTwoThreeSpectrum3570.graph sourceMap4143=true := by decide +kernel
theorem fusedMap4143_checked : acceptsGraphIso
    (fused (graph core4143) (root 8) 2 2) DegreeTwoThreeSpectrum2751.graph fusedMap4143=true := by decide +kernel
theorem certified4143 : Certified (graph core4143) (root 8) 2 2 :=
  of_native_maps core4143 DegreeTwoThreeSpectrum3570.graph DegreeTwoThreeSpectrum2751.graph
    sourceMap4143 fusedMap4143 sourceMap4143_checked fusedMap4143_checked
    DegreeTwoThreeFiniteComparisons.comparison4143
#print axioms sourceMap4143_checked
#print axioms fusedMap4143_checked
#print axioms certified4143
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
