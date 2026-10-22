/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4115 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap4115 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4115 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4115_checked : acceptsGraphIso
    (source (graph core4115) (root 8) 2 2) DegreeTwoThreeSpectrum3626.graph sourceMap4115=true := by decide +kernel
theorem fusedMap4115_checked : acceptsGraphIso
    (fused (graph core4115) (root 8) 2 2) DegreeTwoThreeSpectrum2389.graph fusedMap4115=true := by decide +kernel
theorem certified4115 : Certified (graph core4115) (root 8) 2 2 :=
  of_native_maps core4115 DegreeTwoThreeSpectrum3626.graph DegreeTwoThreeSpectrum2389.graph
    sourceMap4115 fusedMap4115 sourceMap4115_checked fusedMap4115_checked
    DegreeTwoThreeFiniteComparisons.comparison4115
#print axioms sourceMap4115_checked
#print axioms fusedMap4115_checked
#print axioms certified4115
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
