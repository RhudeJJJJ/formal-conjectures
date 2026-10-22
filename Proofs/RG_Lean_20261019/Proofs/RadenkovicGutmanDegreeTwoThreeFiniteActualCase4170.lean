/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4170 : Family 8 := level8.get ⟨215,by decide⟩
def sourceMap4170 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4170 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4170_checked : acceptsGraphIso
    (source (graph core4170) (root 8) 2 2) DegreeTwoThreeSpectrum3800.graph sourceMap4170=true := by decide +kernel
theorem fusedMap4170_checked : acceptsGraphIso
    (fused (graph core4170) (root 8) 2 2) DegreeTwoThreeSpectrum2520.graph fusedMap4170=true := by decide +kernel
theorem certified4170 : Certified (graph core4170) (root 8) 2 2 :=
  of_native_maps core4170 DegreeTwoThreeSpectrum3800.graph DegreeTwoThreeSpectrum2520.graph
    sourceMap4170 fusedMap4170 sourceMap4170_checked fusedMap4170_checked
    DegreeTwoThreeFiniteComparisons.comparison4170
#print axioms sourceMap4170_checked
#print axioms fusedMap4170_checked
#print axioms certified4170
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
