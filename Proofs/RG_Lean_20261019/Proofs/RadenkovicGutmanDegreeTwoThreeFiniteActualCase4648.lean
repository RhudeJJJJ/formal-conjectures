/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4648 : Family 10 := level10.get ⟨736,by decide⟩
def sourceMap4648 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4648 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4648_checked : acceptsGraphIso
    (source (graph core4648) (root 10) 2 2) DegreeTwoThreeSpectrum7396.graph sourceMap4648=true := by decide +kernel
theorem fusedMap4648_checked : acceptsGraphIso
    (fused (graph core4648) (root 10) 2 2) DegreeTwoThreeSpectrum5494.graph fusedMap4648=true := by decide +kernel
theorem certified4648 : Certified (graph core4648) (root 10) 2 2 :=
  of_native_maps core4648 DegreeTwoThreeSpectrum7396.graph DegreeTwoThreeSpectrum5494.graph
    sourceMap4648 fusedMap4648 sourceMap4648_checked fusedMap4648_checked
    DegreeTwoThreeFiniteComparisons.comparison4648
#print axioms sourceMap4648_checked
#print axioms fusedMap4648_checked
#print axioms certified4648
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
