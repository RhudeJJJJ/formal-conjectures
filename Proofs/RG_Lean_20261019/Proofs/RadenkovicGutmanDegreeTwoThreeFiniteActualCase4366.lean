/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4366 : Family 9 := level9.get ⟨513,by decide⟩
def sourceMap4366 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,1,2,3,4,5,6,7,8,9] (sourceLabel 9 2 2 v)
def fusedMap4366 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4366_checked : acceptsGraphIso
    (source (graph core4366) (root 9) 2 2) DegreeTwoThreeSpectrum4863.graph sourceMap4366=true := by decide +kernel
theorem fusedMap4366_checked : acceptsGraphIso
    (fused (graph core4366) (root 9) 2 2) DegreeTwoThreeSpectrum4600.graph fusedMap4366=true := by decide +kernel
theorem certified4366 : Certified (graph core4366) (root 9) 2 2 :=
  of_native_maps core4366 DegreeTwoThreeSpectrum4863.graph DegreeTwoThreeSpectrum4600.graph
    sourceMap4366 fusedMap4366 sourceMap4366_checked fusedMap4366_checked
    DegreeTwoThreeFiniteComparisons.comparison4366
#print axioms sourceMap4366_checked
#print axioms fusedMap4366_checked
#print axioms certified4366
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
