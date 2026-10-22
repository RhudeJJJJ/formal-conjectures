/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4882 : Family 10 := level10.get ⟨1330,by decide⟩
def sourceMap4882 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4882 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4882_checked : acceptsGraphIso
    (source (graph core4882) (root 10) 2 2) DegreeTwoThreeSpectrum7410.graph sourceMap4882=true := by decide +kernel
theorem fusedMap4882_checked : acceptsGraphIso
    (fused (graph core4882) (root 10) 2 2) DegreeTwoThreeSpectrum6642.graph fusedMap4882=true := by decide +kernel
theorem certified4882 : Certified (graph core4882) (root 10) 2 2 :=
  of_native_maps core4882 DegreeTwoThreeSpectrum7410.graph DegreeTwoThreeSpectrum6642.graph
    sourceMap4882 fusedMap4882 sourceMap4882_checked fusedMap4882_checked
    DegreeTwoThreeFiniteComparisons.comparison4882
#print axioms sourceMap4882_checked
#print axioms fusedMap4882_checked
#print axioms certified4882
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
