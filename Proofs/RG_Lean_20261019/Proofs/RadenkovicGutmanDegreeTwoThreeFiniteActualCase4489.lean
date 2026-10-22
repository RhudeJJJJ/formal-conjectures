/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4489 : Family 10 := level10.get ⟨253,by decide⟩
def sourceMap4489 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4489 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4489_checked : acceptsGraphIso
    (source (graph core4489) (root 10) 2 2) DegreeTwoThreeSpectrum6411.graph sourceMap4489=true := by decide +kernel
theorem fusedMap4489_checked : acceptsGraphIso
    (fused (graph core4489) (root 10) 2 2) DegreeTwoThreeSpectrum5350.graph fusedMap4489=true := by decide +kernel
theorem certified4489 : Certified (graph core4489) (root 10) 2 2 :=
  of_native_maps core4489 DegreeTwoThreeSpectrum6411.graph DegreeTwoThreeSpectrum5350.graph
    sourceMap4489 fusedMap4489 sourceMap4489_checked fusedMap4489_checked
    DegreeTwoThreeFiniteComparisons.comparison4489
#print axioms sourceMap4489_checked
#print axioms fusedMap4489_checked
#print axioms certified4489
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
