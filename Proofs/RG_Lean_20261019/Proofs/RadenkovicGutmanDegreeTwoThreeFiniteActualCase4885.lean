/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4885 : Family 10 := level10.get ⟨1336,by decide⟩
def sourceMap4885 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4885 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4885_checked : acceptsGraphIso
    (source (graph core4885) (root 10) 2 2) DegreeTwoThreeSpectrum7423.graph sourceMap4885=true := by decide +kernel
theorem fusedMap4885_checked : acceptsGraphIso
    (fused (graph core4885) (root 10) 2 2) DegreeTwoThreeSpectrum6654.graph fusedMap4885=true := by decide +kernel
theorem certified4885 : Certified (graph core4885) (root 10) 2 2 :=
  of_native_maps core4885 DegreeTwoThreeSpectrum7423.graph DegreeTwoThreeSpectrum6654.graph
    sourceMap4885 fusedMap4885 sourceMap4885_checked fusedMap4885_checked
    DegreeTwoThreeFiniteComparisons.comparison4885
#print axioms sourceMap4885_checked
#print axioms fusedMap4885_checked
#print axioms certified4885
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
