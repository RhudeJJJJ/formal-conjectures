/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4156 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap4156 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 2 2 v)
def fusedMap4156 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4156_checked : acceptsGraphIso
    (source (graph core4156) (root 8) 2 2) DegreeTwoThreeSpectrum3287.graph sourceMap4156=true := by decide +kernel
theorem fusedMap4156_checked : acceptsGraphIso
    (fused (graph core4156) (root 8) 2 2) DegreeTwoThreeSpectrum2948.graph fusedMap4156=true := by decide +kernel
theorem certified4156 : Certified (graph core4156) (root 8) 2 2 :=
  of_native_maps core4156 DegreeTwoThreeSpectrum3287.graph DegreeTwoThreeSpectrum2948.graph
    sourceMap4156 fusedMap4156 sourceMap4156_checked fusedMap4156_checked
    DegreeTwoThreeFiniteComparisons.comparison4156
#print axioms sourceMap4156_checked
#print axioms fusedMap4156_checked
#print axioms certified4156
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
