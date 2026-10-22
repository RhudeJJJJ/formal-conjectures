/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4762 : Family 10 := level10.get ⟨1035,by decide⟩
def sourceMap4762 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4762 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4762_checked : acceptsGraphIso
    (source (graph core4762) (root 10) 2 2) DegreeTwoThreeSpectrum7112.graph sourceMap4762=true := by decide +kernel
theorem fusedMap4762_checked : acceptsGraphIso
    (fused (graph core4762) (root 10) 2 2) DegreeTwoThreeSpectrum6054.graph fusedMap4762=true := by decide +kernel
theorem certified4762 : Certified (graph core4762) (root 10) 2 2 :=
  of_native_maps core4762 DegreeTwoThreeSpectrum7112.graph DegreeTwoThreeSpectrum6054.graph
    sourceMap4762 fusedMap4762 sourceMap4762_checked fusedMap4762_checked
    DegreeTwoThreeFiniteComparisons.comparison4762
#print axioms sourceMap4762_checked
#print axioms fusedMap4762_checked
#print axioms certified4762
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
