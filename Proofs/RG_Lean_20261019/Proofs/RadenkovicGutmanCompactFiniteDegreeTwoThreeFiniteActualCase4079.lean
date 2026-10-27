/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4079 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap4079 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4079 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4079_checked : acceptsGraphIso
    (source (graph core4079) (root 7) 2 2) DegreeTwoThreeSpectrum2253.graph sourceMap4079=true := by decide +kernel
theorem fusedMap4079_checked : acceptsGraphIso
    (fused (graph core4079) (root 7) 2 2) DegreeTwoThreeSpectrum1740.graph fusedMap4079=true := by decide +kernel
theorem certified4079 : Certified (graph core4079) (root 7) 2 2 :=
  of_native_maps core4079 DegreeTwoThreeSpectrum2253.graph DegreeTwoThreeSpectrum1740.graph
    sourceMap4079 fusedMap4079 sourceMap4079_checked fusedMap4079_checked
    DegreeTwoThreeFiniteComparisons.comparison4079
#print axioms sourceMap4079_checked
#print axioms fusedMap4079_checked
#print axioms certified4079
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
