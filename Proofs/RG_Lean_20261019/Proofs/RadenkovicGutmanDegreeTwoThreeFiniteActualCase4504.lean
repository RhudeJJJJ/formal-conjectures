/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4504 : Family 10 := level10.get ⟨301,by decide⟩
def sourceMap4504 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4504 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4504_checked : acceptsGraphIso
    (source (graph core4504) (root 10) 2 2) DegreeTwoThreeSpectrum6576.graph sourceMap4504=true := by decide +kernel
theorem fusedMap4504_checked : acceptsGraphIso
    (fused (graph core4504) (root 10) 2 2) DegreeTwoThreeSpectrum5477.graph fusedMap4504=true := by decide +kernel
theorem certified4504 : Certified (graph core4504) (root 10) 2 2 :=
  of_native_maps core4504 DegreeTwoThreeSpectrum6576.graph DegreeTwoThreeSpectrum5477.graph
    sourceMap4504 fusedMap4504 sourceMap4504_checked fusedMap4504_checked
    DegreeTwoThreeFiniteComparisons.comparison4504
#print axioms sourceMap4504_checked
#print axioms fusedMap4504_checked
#print axioms certified4504
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
