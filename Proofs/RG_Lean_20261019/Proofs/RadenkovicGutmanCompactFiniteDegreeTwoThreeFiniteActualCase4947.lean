/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4947 : Family 10 := level10.get ⟨1477,by decide⟩
def sourceMap4947 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4947 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4947_checked : acceptsGraphIso
    (source (graph core4947) (root 10) 2 2) DegreeTwoThreeSpectrum7149.graph sourceMap4947=true := by decide +kernel
theorem fusedMap4947_checked : acceptsGraphIso
    (fused (graph core4947) (root 10) 2 2) DegreeTwoThreeSpectrum6964.graph fusedMap4947=true := by decide +kernel
theorem certified4947 : Certified (graph core4947) (root 10) 2 2 :=
  of_native_maps core4947 DegreeTwoThreeSpectrum7149.graph DegreeTwoThreeSpectrum6964.graph
    sourceMap4947 fusedMap4947 sourceMap4947_checked fusedMap4947_checked
    DegreeTwoThreeFiniteComparisons.comparison4947
#print axioms sourceMap4947_checked
#print axioms fusedMap4947_checked
#print axioms certified4947
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
