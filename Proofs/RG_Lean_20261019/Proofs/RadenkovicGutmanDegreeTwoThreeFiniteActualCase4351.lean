/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4351 : Family 9 := level9.get ⟨478,by decide⟩
def sourceMap4351 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4351 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4351_checked : acceptsGraphIso
    (source (graph core4351) (root 9) 2 2) DegreeTwoThreeSpectrum4763.graph sourceMap4351=true := by decide +kernel
theorem fusedMap4351_checked : acceptsGraphIso
    (fused (graph core4351) (root 9) 2 2) DegreeTwoThreeSpectrum4519.graph fusedMap4351=true := by decide +kernel
theorem certified4351 : Certified (graph core4351) (root 9) 2 2 :=
  of_native_maps core4351 DegreeTwoThreeSpectrum4763.graph DegreeTwoThreeSpectrum4519.graph
    sourceMap4351 fusedMap4351 sourceMap4351_checked fusedMap4351_checked
    DegreeTwoThreeFiniteComparisons.comparison4351
#print axioms sourceMap4351_checked
#print axioms fusedMap4351_checked
#print axioms certified4351
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
