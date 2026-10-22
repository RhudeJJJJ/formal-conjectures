/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4550 : Family 10 := level10.get ⟨452,by decide⟩
def sourceMap4550 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,9,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4550 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4550_checked : acceptsGraphIso
    (source (graph core4550) (root 10) 2 2) DegreeTwoThreeSpectrum6834.graph sourceMap4550=true := by decide +kernel
theorem fusedMap4550_checked : acceptsGraphIso
    (fused (graph core4550) (root 10) 2 2) DegreeTwoThreeSpectrum5880.graph fusedMap4550=true := by decide +kernel
theorem certified4550 : Certified (graph core4550) (root 10) 2 2 :=
  of_native_maps core4550 DegreeTwoThreeSpectrum6834.graph DegreeTwoThreeSpectrum5880.graph
    sourceMap4550 fusedMap4550 sourceMap4550_checked fusedMap4550_checked
    DegreeTwoThreeFiniteComparisons.comparison4550
#print axioms sourceMap4550_checked
#print axioms fusedMap4550_checked
#print axioms certified4550
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
