/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4076 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap4076 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,7,8,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4076 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4076_checked : acceptsGraphIso
    (source (graph core4076) (root 7) 2 2) DegreeTwoThreeSpectrum2181.graph sourceMap4076=true := by decide +kernel
theorem fusedMap4076_checked : acceptsGraphIso
    (fused (graph core4076) (root 7) 2 2) DegreeTwoThreeSpectrum1892.graph fusedMap4076=true := by decide +kernel
theorem certified4076 : Certified (graph core4076) (root 7) 2 2 :=
  of_native_maps core4076 DegreeTwoThreeSpectrum2181.graph DegreeTwoThreeSpectrum1892.graph
    sourceMap4076 fusedMap4076 sourceMap4076_checked fusedMap4076_checked
    DegreeTwoThreeFiniteComparisons.comparison4076
#print axioms sourceMap4076_checked
#print axioms fusedMap4076_checked
#print axioms certified4076
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
