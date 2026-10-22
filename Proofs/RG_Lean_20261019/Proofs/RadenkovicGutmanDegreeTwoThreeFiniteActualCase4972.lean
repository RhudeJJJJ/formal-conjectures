/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4972 : Family 10 := level10.get ⟨1554,by decide⟩
def sourceMap4972 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4972 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4972_checked : acceptsGraphIso
    (source (graph core4972) (root 10) 2 2) DegreeTwoThreeSpectrum7573.graph sourceMap4972=true := by decide +kernel
theorem fusedMap4972_checked : acceptsGraphIso
    (fused (graph core4972) (root 10) 2 2) DegreeTwoThreeSpectrum6010.graph fusedMap4972=true := by decide +kernel
theorem certified4972 : Certified (graph core4972) (root 10) 2 2 :=
  of_native_maps core4972 DegreeTwoThreeSpectrum7573.graph DegreeTwoThreeSpectrum6010.graph
    sourceMap4972 fusedMap4972 sourceMap4972_checked fusedMap4972_checked
    DegreeTwoThreeFiniteComparisons.comparison4972
#print axioms sourceMap4972_checked
#print axioms fusedMap4972_checked
#print axioms certified4972
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
