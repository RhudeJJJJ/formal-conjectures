/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4694 : Family 10 := level10.get ⟨866,by decide⟩
def sourceMap4694 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4694 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4694_checked : acceptsGraphIso
    (source (graph core4694) (root 10) 2 2) DegreeTwoThreeSpectrum7533.graph sourceMap4694=true := by decide +kernel
theorem fusedMap4694_checked : acceptsGraphIso
    (fused (graph core4694) (root 10) 2 2) DegreeTwoThreeSpectrum5706.graph fusedMap4694=true := by decide +kernel
theorem certified4694 : Certified (graph core4694) (root 10) 2 2 :=
  of_native_maps core4694 DegreeTwoThreeSpectrum7533.graph DegreeTwoThreeSpectrum5706.graph
    sourceMap4694 fusedMap4694 sourceMap4694_checked fusedMap4694_checked
    DegreeTwoThreeFiniteComparisons.comparison4694
#print axioms sourceMap4694_checked
#print axioms fusedMap4694_checked
#print axioms certified4694
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
