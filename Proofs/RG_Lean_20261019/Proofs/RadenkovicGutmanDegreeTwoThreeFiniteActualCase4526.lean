/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4526 : Family 10 := level10.get ⟨375,by decide⟩
def sourceMap4526 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4526 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4526_checked : acceptsGraphIso
    (source (graph core4526) (root 10) 2 2) DegreeTwoThreeSpectrum6838.graph sourceMap4526=true := by decide +kernel
theorem fusedMap4526_checked : acceptsGraphIso
    (fused (graph core4526) (root 10) 2 2) DegreeTwoThreeSpectrum5688.graph fusedMap4526=true := by decide +kernel
theorem certified4526 : Certified (graph core4526) (root 10) 2 2 :=
  of_native_maps core4526 DegreeTwoThreeSpectrum6838.graph DegreeTwoThreeSpectrum5688.graph
    sourceMap4526 fusedMap4526 sourceMap4526_checked fusedMap4526_checked
    DegreeTwoThreeFiniteComparisons.comparison4526
#print axioms sourceMap4526_checked
#print axioms fusedMap4526_checked
#print axioms certified4526
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
