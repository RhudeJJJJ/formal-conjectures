/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4065 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap4065 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,8,9,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap4065 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4065_checked : acceptsGraphIso
    (source (graph core4065) (root 7) 2 2) DegreeTwoThreeSpectrum2182.graph sourceMap4065=true := by decide +kernel
theorem fusedMap4065_checked : acceptsGraphIso
    (fused (graph core4065) (root 7) 2 2) DegreeTwoThreeSpectrum1735.graph fusedMap4065=true := by decide +kernel
theorem certified4065 : Certified (graph core4065) (root 7) 2 2 :=
  of_native_maps core4065 DegreeTwoThreeSpectrum2182.graph DegreeTwoThreeSpectrum1735.graph
    sourceMap4065 fusedMap4065 sourceMap4065_checked fusedMap4065_checked
    DegreeTwoThreeFiniteComparisons.comparison4065
#print axioms sourceMap4065_checked
#print axioms fusedMap4065_checked
#print axioms certified4065
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
