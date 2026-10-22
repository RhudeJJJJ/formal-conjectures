/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4283 : Family 9 := level9.get ⟨305,by decide⟩
def sourceMap4283 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4283 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4283_checked : acceptsGraphIso
    (source (graph core4283) (root 9) 2 2) DegreeTwoThreeSpectrum4872.graph sourceMap4283=true := by decide +kernel
theorem fusedMap4283_checked : acceptsGraphIso
    (fused (graph core4283) (root 9) 2 2) DegreeTwoThreeSpectrum4140.graph fusedMap4283=true := by decide +kernel
theorem certified4283 : Certified (graph core4283) (root 9) 2 2 :=
  of_native_maps core4283 DegreeTwoThreeSpectrum4872.graph DegreeTwoThreeSpectrum4140.graph
    sourceMap4283 fusedMap4283 sourceMap4283_checked fusedMap4283_checked
    DegreeTwoThreeFiniteComparisons.comparison4283
#print axioms sourceMap4283_checked
#print axioms fusedMap4283_checked
#print axioms certified4283
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
