/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4082 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap4082 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4082 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4082_checked : acceptsGraphIso
    (source (graph core4082) (root 7) 2 2) DegreeTwoThreeSpectrum2271.graph sourceMap4082=true := by decide +kernel
theorem fusedMap4082_checked : acceptsGraphIso
    (fused (graph core4082) (root 7) 2 2) DegreeTwoThreeSpectrum1759.graph fusedMap4082=true := by decide +kernel
theorem certified4082 : Certified (graph core4082) (root 7) 2 2 :=
  of_native_maps core4082 DegreeTwoThreeSpectrum2271.graph DegreeTwoThreeSpectrum1759.graph
    sourceMap4082 fusedMap4082 sourceMap4082_checked fusedMap4082_checked
    DegreeTwoThreeFiniteComparisons.comparison4082
#print axioms sourceMap4082_checked
#print axioms fusedMap4082_checked
#print axioms certified4082
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
