/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4498 : Family 10 := level10.get ⟨278,by decide⟩
def sourceMap4498 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,16,14,15,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4498 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4498_checked : acceptsGraphIso
    (source (graph core4498) (root 10) 2 2) DegreeTwoThreeSpectrum6456.graph sourceMap4498=true := by decide +kernel
theorem fusedMap4498_checked : acceptsGraphIso
    (fused (graph core4498) (root 10) 2 2) DegreeTwoThreeSpectrum5411.graph fusedMap4498=true := by decide +kernel
theorem certified4498 : Certified (graph core4498) (root 10) 2 2 :=
  of_native_maps core4498 DegreeTwoThreeSpectrum6456.graph DegreeTwoThreeSpectrum5411.graph
    sourceMap4498 fusedMap4498 sourceMap4498_checked fusedMap4498_checked
    DegreeTwoThreeFiniteComparisons.comparison4498
#print axioms sourceMap4498_checked
#print axioms fusedMap4498_checked
#print axioms certified4498
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
