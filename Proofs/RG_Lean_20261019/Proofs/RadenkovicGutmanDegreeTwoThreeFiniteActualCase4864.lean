/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4864 : Family 10 := level10.get ⟨1285,by decide⟩
def sourceMap4864 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4864 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4864_checked : acceptsGraphIso
    (source (graph core4864) (root 10) 2 2) DegreeTwoThreeSpectrum7367.graph sourceMap4864=true := by decide +kernel
theorem fusedMap4864_checked : acceptsGraphIso
    (fused (graph core4864) (root 10) 2 2) DegreeTwoThreeSpectrum6555.graph fusedMap4864=true := by decide +kernel
theorem certified4864 : Certified (graph core4864) (root 10) 2 2 :=
  of_native_maps core4864 DegreeTwoThreeSpectrum7367.graph DegreeTwoThreeSpectrum6555.graph
    sourceMap4864 fusedMap4864 sourceMap4864_checked fusedMap4864_checked
    DegreeTwoThreeFiniteComparisons.comparison4864
#print axioms sourceMap4864_checked
#print axioms fusedMap4864_checked
#print axioms certified4864
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
