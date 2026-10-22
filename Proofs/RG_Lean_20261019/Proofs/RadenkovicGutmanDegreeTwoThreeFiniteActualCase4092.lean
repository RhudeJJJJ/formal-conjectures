/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4092 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap4092 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,11,12,13,5,6,7,8,9,10] (sourceLabel 7 2 2 v)
def fusedMap4092 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4092_checked : acceptsGraphIso
    (source (graph core4092) (root 7) 2 2) DegreeTwoThreeSpectrum2303.graph sourceMap4092=true := by decide +kernel
theorem fusedMap4092_checked : acceptsGraphIso
    (fused (graph core4092) (root 7) 2 2) DegreeTwoThreeSpectrum1831.graph fusedMap4092=true := by decide +kernel
theorem certified4092 : Certified (graph core4092) (root 7) 2 2 :=
  of_native_maps core4092 DegreeTwoThreeSpectrum2303.graph DegreeTwoThreeSpectrum1831.graph
    sourceMap4092 fusedMap4092 sourceMap4092_checked fusedMap4092_checked
    DegreeTwoThreeFiniteComparisons.comparison4092
#print axioms sourceMap4092_checked
#print axioms fusedMap4092_checked
#print axioms certified4092
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
