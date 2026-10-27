/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4068 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap4068 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4068 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4068_checked : acceptsGraphIso
    (source (graph core4068) (root 7) 2 2) DegreeTwoThreeSpectrum2060.graph sourceMap4068=true := by decide +kernel
theorem fusedMap4068_checked : acceptsGraphIso
    (fused (graph core4068) (root 7) 2 2) DegreeTwoThreeSpectrum1784.graph fusedMap4068=true := by decide +kernel
theorem certified4068 : Certified (graph core4068) (root 7) 2 2 :=
  of_native_maps core4068 DegreeTwoThreeSpectrum2060.graph DegreeTwoThreeSpectrum1784.graph
    sourceMap4068 fusedMap4068 sourceMap4068_checked fusedMap4068_checked
    DegreeTwoThreeFiniteComparisons.comparison4068
#print axioms sourceMap4068_checked
#print axioms fusedMap4068_checked
#print axioms certified4068
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
