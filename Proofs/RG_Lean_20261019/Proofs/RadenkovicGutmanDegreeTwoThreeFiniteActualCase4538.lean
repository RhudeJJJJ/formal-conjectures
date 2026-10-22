/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4538 : Family 10 := level10.get ⟨414,by decide⟩
def sourceMap4538 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4538 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4538_checked : acceptsGraphIso
    (source (graph core4538) (root 10) 2 2) DegreeTwoThreeSpectrum6811.graph sourceMap4538=true := by decide +kernel
theorem fusedMap4538_checked : acceptsGraphIso
    (fused (graph core4538) (root 10) 2 2) DegreeTwoThreeSpectrum5792.graph fusedMap4538=true := by decide +kernel
theorem certified4538 : Certified (graph core4538) (root 10) 2 2 :=
  of_native_maps core4538 DegreeTwoThreeSpectrum6811.graph DegreeTwoThreeSpectrum5792.graph
    sourceMap4538 fusedMap4538 sourceMap4538_checked fusedMap4538_checked
    DegreeTwoThreeFiniteComparisons.comparison4538
#print axioms sourceMap4538_checked
#print axioms fusedMap4538_checked
#print axioms certified4538
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
