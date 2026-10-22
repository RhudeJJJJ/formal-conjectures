/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4101 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap4101 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4101 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 2 2 v)
theorem sourceMap4101_checked : acceptsGraphIso
    (source (graph core4101) (root 8) 2 2) DegreeTwoThreeSpectrum2818.graph sourceMap4101=true := by decide +kernel
theorem fusedMap4101_checked : acceptsGraphIso
    (fused (graph core4101) (root 8) 2 2) DegreeTwoThreeSpectrum2427.graph fusedMap4101=true := by decide +kernel
theorem certified4101 : Certified (graph core4101) (root 8) 2 2 :=
  of_native_maps core4101 DegreeTwoThreeSpectrum2818.graph DegreeTwoThreeSpectrum2427.graph
    sourceMap4101 fusedMap4101 sourceMap4101_checked fusedMap4101_checked
    DegreeTwoThreeFiniteComparisons.comparison4101
#print axioms sourceMap4101_checked
#print axioms fusedMap4101_checked
#print axioms certified4101
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
