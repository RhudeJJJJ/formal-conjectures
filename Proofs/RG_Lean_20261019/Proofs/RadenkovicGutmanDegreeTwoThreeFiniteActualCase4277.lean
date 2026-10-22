/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4277 : Family 9 := level9.get ⟨294,by decide⟩
def sourceMap4277 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4277 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4277_checked : acceptsGraphIso
    (source (graph core4277) (root 9) 2 2) DegreeTwoThreeSpectrum4897.graph sourceMap4277=true := by decide +kernel
theorem fusedMap4277_checked : acceptsGraphIso
    (fused (graph core4277) (root 9) 2 2) DegreeTwoThreeSpectrum4123.graph fusedMap4277=true := by decide +kernel
theorem certified4277 : Certified (graph core4277) (root 9) 2 2 :=
  of_native_maps core4277 DegreeTwoThreeSpectrum4897.graph DegreeTwoThreeSpectrum4123.graph
    sourceMap4277 fusedMap4277 sourceMap4277_checked fusedMap4277_checked
    DegreeTwoThreeFiniteComparisons.comparison4277
#print axioms sourceMap4277_checked
#print axioms fusedMap4277_checked
#print axioms certified4277
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
