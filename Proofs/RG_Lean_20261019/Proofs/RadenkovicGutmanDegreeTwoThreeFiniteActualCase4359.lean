/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4359 : Family 9 := level9.get ⟨500,by decide⟩
def sourceMap4359 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4359 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4359_checked : acceptsGraphIso
    (source (graph core4359) (root 9) 2 2) DegreeTwoThreeSpectrum4887.graph sourceMap4359=true := by decide +kernel
theorem fusedMap4359_checked : acceptsGraphIso
    (fused (graph core4359) (root 9) 2 2) DegreeTwoThreeSpectrum4578.graph fusedMap4359=true := by decide +kernel
theorem certified4359 : Certified (graph core4359) (root 9) 2 2 :=
  of_native_maps core4359 DegreeTwoThreeSpectrum4887.graph DegreeTwoThreeSpectrum4578.graph
    sourceMap4359 fusedMap4359 sourceMap4359_checked fusedMap4359_checked
    DegreeTwoThreeFiniteComparisons.comparison4359
#print axioms sourceMap4359_checked
#print axioms fusedMap4359_checked
#print axioms certified4359
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
