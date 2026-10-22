/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4117 : Family 8 := level8.get ⟨81,by decide⟩
def sourceMap4117 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4117 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4117_checked : acceptsGraphIso
    (source (graph core4117) (root 8) 2 2) DegreeTwoThreeSpectrum3617.graph sourceMap4117=true := by decide +kernel
theorem fusedMap4117_checked : acceptsGraphIso
    (fused (graph core4117) (root 8) 2 2) DegreeTwoThreeSpectrum2399.graph fusedMap4117=true := by decide +kernel
theorem certified4117 : Certified (graph core4117) (root 8) 2 2 :=
  of_native_maps core4117 DegreeTwoThreeSpectrum3617.graph DegreeTwoThreeSpectrum2399.graph
    sourceMap4117 fusedMap4117 sourceMap4117_checked fusedMap4117_checked
    DegreeTwoThreeFiniteComparisons.comparison4117
#print axioms sourceMap4117_checked
#print axioms fusedMap4117_checked
#print axioms certified4117
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
