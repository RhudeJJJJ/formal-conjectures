/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4430 : Family 9 := level9.get ⟨693,by decide⟩
def sourceMap4430 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4430 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4430_checked : acceptsGraphIso
    (source (graph core4430) (root 9) 2 2) DegreeTwoThreeSpectrum4957.graph sourceMap4430=true := by decide +kernel
theorem fusedMap4430_checked : acceptsGraphIso
    (fused (graph core4430) (root 9) 2 2) DegreeTwoThreeSpectrum4671.graph fusedMap4430=true := by decide +kernel
theorem certified4430 : Certified (graph core4430) (root 9) 2 2 :=
  of_native_maps core4430 DegreeTwoThreeSpectrum4957.graph DegreeTwoThreeSpectrum4671.graph
    sourceMap4430 fusedMap4430 sourceMap4430_checked fusedMap4430_checked
    DegreeTwoThreeFiniteComparisons.comparison4430
#print axioms sourceMap4430_checked
#print axioms fusedMap4430_checked
#print axioms certified4430
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
