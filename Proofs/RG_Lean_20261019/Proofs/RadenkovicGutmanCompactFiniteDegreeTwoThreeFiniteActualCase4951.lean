/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4951 : Family 10 := level10.get ⟨1485,by decide⟩
def sourceMap4951 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4951 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4951_checked : acceptsGraphIso
    (source (graph core4951) (root 10) 2 2) DegreeTwoThreeSpectrum7485.graph sourceMap4951=true := by decide +kernel
theorem fusedMap4951_checked : acceptsGraphIso
    (fused (graph core4951) (root 10) 2 2) DegreeTwoThreeSpectrum6978.graph fusedMap4951=true := by decide +kernel
theorem certified4951 : Certified (graph core4951) (root 10) 2 2 :=
  of_native_maps core4951 DegreeTwoThreeSpectrum7485.graph DegreeTwoThreeSpectrum6978.graph
    sourceMap4951 fusedMap4951 sourceMap4951_checked fusedMap4951_checked
    DegreeTwoThreeFiniteComparisons.comparison4951
#print axioms sourceMap4951_checked
#print axioms fusedMap4951_checked
#print axioms certified4951
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
