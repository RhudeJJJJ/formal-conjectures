/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4688 : Family 10 := level10.get ⟨849,by decide⟩
def sourceMap4688 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4688 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4688_checked : acceptsGraphIso
    (source (graph core4688) (root 10) 2 2) DegreeTwoThreeSpectrum7527.graph sourceMap4688=true := by decide +kernel
theorem fusedMap4688_checked : acceptsGraphIso
    (fused (graph core4688) (root 10) 2 2) DegreeTwoThreeSpectrum5682.graph fusedMap4688=true := by decide +kernel
theorem certified4688 : Certified (graph core4688) (root 10) 2 2 :=
  of_native_maps core4688 DegreeTwoThreeSpectrum7527.graph DegreeTwoThreeSpectrum5682.graph
    sourceMap4688 fusedMap4688 sourceMap4688_checked fusedMap4688_checked
    DegreeTwoThreeFiniteComparisons.comparison4688
#print axioms sourceMap4688_checked
#print axioms fusedMap4688_checked
#print axioms certified4688
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
