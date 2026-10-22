/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4360 : Family 9 := level9.get ⟨502,by decide⟩
def sourceMap4360 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4360 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4360_checked : acceptsGraphIso
    (source (graph core4360) (root 9) 2 2) DegreeTwoThreeSpectrum4888.graph sourceMap4360=true := by decide +kernel
theorem fusedMap4360_checked : acceptsGraphIso
    (fused (graph core4360) (root 9) 2 2) DegreeTwoThreeSpectrum4580.graph fusedMap4360=true := by decide +kernel
theorem certified4360 : Certified (graph core4360) (root 9) 2 2 :=
  of_native_maps core4360 DegreeTwoThreeSpectrum4888.graph DegreeTwoThreeSpectrum4580.graph
    sourceMap4360 fusedMap4360 sourceMap4360_checked fusedMap4360_checked
    DegreeTwoThreeFiniteComparisons.comparison4360
#print axioms sourceMap4360_checked
#print axioms fusedMap4360_checked
#print axioms certified4360
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
