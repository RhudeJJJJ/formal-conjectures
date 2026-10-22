/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4085 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap4085 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap4085 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4085_checked : acceptsGraphIso
    (source (graph core4085) (root 7) 2 2) DegreeTwoThreeSpectrum2283.graph sourceMap4085=true := by decide +kernel
theorem fusedMap4085_checked : acceptsGraphIso
    (fused (graph core4085) (root 7) 2 2) DegreeTwoThreeSpectrum1775.graph fusedMap4085=true := by decide +kernel
theorem certified4085 : Certified (graph core4085) (root 7) 2 2 :=
  of_native_maps core4085 DegreeTwoThreeSpectrum2283.graph DegreeTwoThreeSpectrum1775.graph
    sourceMap4085 fusedMap4085 sourceMap4085_checked fusedMap4085_checked
    DegreeTwoThreeFiniteComparisons.comparison4085
#print axioms sourceMap4085_checked
#print axioms fusedMap4085_checked
#print axioms certified4085
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
